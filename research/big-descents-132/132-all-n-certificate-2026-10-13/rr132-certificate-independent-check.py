"""Independent exact-rational verification of B132 compact certificate data.

This file imports neither the search script nor its dyadic arithmetic.
It generates no polynomial rows and writes only a verification receipt.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import hashlib
import json
import sys
import time


class Box:
    def __init__(self, left=0, right=None):
        self.left = Q(left)
        self.right = self.left if right is None else Q(right)
        assert self.left <= self.right

    def __add__(self, other):
        other = box(other)
        return Box(self.left + other.left, self.right + other.right)

    __radd__ = __add__

    def __neg__(self):
        return Box(-self.right, -self.left)

    def __sub__(self, other):
        return self + -box(other)

    def __rsub__(self, other):
        return box(other) + -self

    def __mul__(self, other):
        other = box(other)
        products = [a * b for a in (self.left, self.right)
                    for b in (other.left, other.right)]
        return Box(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = box(other)
        assert not other.left <= 0 <= other.right, 'division interval meets zero'
        values = [a / b for a in (self.left, self.right)
                  for b in (other.left, other.right)]
        return Box(min(values), max(values))

    def __rtruediv__(self, other):
        return box(other) / self

    def square(self):
        endpoints = [self.left ** 2, self.right ** 2]
        lower = 0 if self.left <= 0 <= self.right else min(endpoints)
        return Box(lower, max(endpoints))

    def power(self, exponent):
        assert exponent >= 0
        if exponent == 0:
            return Box(1)
        if exponent % 2 == 0:
            return self.square().power(exponent // 2)
        return self * self.power(exponent - 1)

    def sqrt_enclosure(self, precision):
        assert self.left >= 0
        scale = 1 << precision
        a = self.left * scale * scale
        b = self.right * scale * scale
        lower = isqrt(a.numerator // a.denominator)
        upper = isqrt(b.numerator // b.denominator)
        if Q(upper * upper) < b:
            upper += 1
        result = Box(Q(lower, scale), Q(upper, scale))
        assert result.left ** 2 <= self.left
        assert result.right ** 2 >= self.right
        return result


def box(value):
    return value if isinstance(value, Box) else Box(value)


class ComplexBox:
    def __init__(self, real=0, imaginary=0):
        self.real, self.imaginary = box(real), box(imaginary)

    def __add__(self, other):
        other = complex_box(other)
        return ComplexBox(self.real + other.real, self.imaginary + other.imaginary)

    __radd__ = __add__

    def __neg__(self):
        return ComplexBox(-self.real, -self.imaginary)

    def __sub__(self, other):
        return self + -complex_box(other)

    def __rsub__(self, other):
        return complex_box(other) + -self

    def __mul__(self, other):
        other = complex_box(other)
        return ComplexBox(self.real * other.real - self.imaginary * other.imaginary,
                          self.real * other.imaginary + self.imaginary * other.real)

    __rmul__ = __mul__

    def norm_squared(self):
        return self.real.square() + self.imaginary.square()

    def __truediv__(self, other):
        other = complex_box(other)
        numerator = self * ComplexBox(other.real, -other.imaginary)
        denominator = other.norm_squared()
        return ComplexBox(numerator.real / denominator,
                          numerator.imaginary / denominator)


def complex_box(value):
    return value if isinstance(value, ComplexBox) else ComplexBox(value)


def dyadic_hull(left, right, precision):
    """Enclose input data only; subsequent arithmetic remains exact Fraction."""
    left, right = Q(left), Q(right)
    scale = 1 << precision
    lower = (left.numerator * scale) // left.denominator
    upper = -((-right.numerator * scale) // right.denominator)
    result = Box(Q(lower, scale), Q(upper, scale))
    assert result.left <= left <= right <= result.right
    return result


def polynomial(parameter, argument):
    return (argument.power(4) + 6 * parameter * argument * argument
            + (4 - 4 * parameter.power(3)) * argument - 3 * parameter * parameter)


def verify_piece(record, precision, degree_threshold):
    scale = 1 << precision
    left, right = map(Q, record['q'])
    assert 0 < left < right
    parameter = dyadic_hull(left, right, precision)
    h = Q(record['h0'])
    assert h > 0
    h_twice = dyadic_hull(4 * h * h, 4 * h * h, precision)
    h_fourth = dyadic_hull(4 * h ** 4, 4 * h ** 4, precision)
    d_coefficient = dyadic_hull(64 * h ** 4, 64 * h ** 4, precision)
    first, second = [Box(Q(int(pair[0]), scale), Q(int(pair[1]), scale))
                     for pair in record['roots']]
    assert first.left < first.right < 0
    assert 0 <= second.left < second.right
    assert polynomial(parameter, Box(first.left)).left > 0
    assert polynomial(parameter, Box(first.right)).right < 0
    assert polynomial(parameter, Box(second.left)).right < 0
    assert polynomial(parameter, Box(second.right)).left > 0

    real_z = -(first + second) / 2
    imaginary_z_squared = (6 * parameter + 3 * first * first / 4
                           + first * second / 2 + 3 * second * second / 4)
    assert imaginary_z_squared.left > 0
    imaginary_z = imaginary_z_squared.sqrt_enclosure(precision)
    z = ComplexBox(real_z, imaginary_z)
    lam = ComplexBox(1) + ComplexBox(parameter) * z
    s = 1 + parameter.power(3)
    a, b = 1 + parameter * first, 1 + parameter * second
    radius_squared = lam.norm_squared()
    da, db, dc = z - first, z - second, ComplexBox(0, 2 * imaginary_z)
    ds = z - parameter * parameter
    fixed_denominator = da * db * dc
    fixed_numerator = ds * ds

    leaves = sorted(record['kernel'], key=lambda item: Q(item[0]))
    assert leaves and Q(leaves[0][0]) == 0
    endpoint = Q(0)
    for leaf in leaves:
        lo, hi = Q(leaf[0]), Q(leaf[1])
        assert lo == endpoint and lo < hi, 'kernel cover gap/overlap'
        endpoint = hi
        shift = lam * ComplexBox(dyadic_hull(lo, hi, precision))
        pole = ds - shift
        numerator = (da - shift) * (db - shift) * (dc - shift) * fixed_numerator
        denominator = fixed_denominator * (pole * pole)
        squared_h = numerator / denominator
        positivity = (squared_h.imaginary.square() + h_twice * squared_h.real
                      - h_fourth)
        assert positivity.left > 0, 'kernel positivity not independently verified'
    assert endpoint >= 1 / left, 'kernel interval does not cover all u'

    distance_a = (lam - a).norm_squared()
    distance_b = (lam - b).norm_squared()
    distance_s = (lam - s).norm_squared()
    d_fourth = (distance_b * (b - a).square() * distance_s.square()
                / (d_coefficient * distance_a * parameter * parameter
                   * imaginary_z_squared * radius_squared * b * b))
    stored_d_upper = Q(int(record['D4'][1]), scale)
    assert d_fourth.right <= stored_d_upper
    rho_squared = b * b / radius_squared
    rho_upper = Q(record['rho_upper'])
    assert 0 < rho_upper < 1
    assert rho_squared.right <= rho_upper ** 2

    peak = int(record['peak'])
    threshold = (3 * rho_upper - 1) / (2 * (1 - rho_upper))
    ceiling = -((-threshold.numerator) // threshold.denominator)
    assert peak == max(degree_threshold, ceiling)
    exact_bound = stored_d_upper * (2 * peak + 1) ** 4 * rho_upper ** (4 * peak)
    assert exact_bound < 1, 'moment maximum is not strictly below one'
    return left, right, len(leaves)


def main():
    source = Path(sys.argv[1])
    raw = source.read_bytes()
    document = json.loads(raw)
    precision, threshold = int(document['bits']), int(document['N'])
    assert precision >= 16 and threshold >= 1
    expected_left, expected_right = map(Q, document['range'])
    pieces = sorted(document['done'], key=lambda item: Q(item['q'][0]))
    endpoint, leaf_count = expected_left, 0
    start = time.monotonic()
    for number, record in enumerate(pieces, 1):
        left, right, count = verify_piece(record, precision, threshold)
        assert left == endpoint, 'parameter cover gap/overlap'
        endpoint, leaf_count = right, leaf_count + count
        if number % 25 == 0:
            print('verified', number, 'parameter intervals and', leaf_count,
                  'kernel rectangles; seconds', round(time.monotonic() - start, 1),
                  flush=True)
    complete = endpoint == expected_right and not document['remaining']
    assert endpoint <= expected_right
    if document['status'] == 'complete':
        assert complete, 'complete marker has incomplete coverage'
    receipt = dict(verified=True, complete=complete,
                   source=str(source), sha256=hashlib.sha256(raw).hexdigest(),
                   arithmetic='exact fractions; independent of dyadic search code',
                   threshold=threshold, parameter_intervals=len(pieces),
                   kernel_rectangles=leaf_count,
                   checked_range=[str(expected_left), str(endpoint)],
                   requested_range=[str(expected_left), str(expected_right)],
                   seconds=round(time.monotonic() - start, 3))
    receipt_path = Path(sys.argv[2]) if len(sys.argv) > 2 else source.with_suffix('.independent-check.json')
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    main()
