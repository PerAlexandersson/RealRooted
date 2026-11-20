#!/usr/bin/env python3
"""Reproduce the path-cube JSON and Lean certificates with exact arithmetic.

The producer and independent replay below are adapted from the supplied Phase 0
spike (generate.py and check.py). The replay reconstructs the mathematical
conditions independently and shares no polynomial arithmetic with the producer.

Run with -B. See --help for generation, reproducibility, and corruption checks.
No build tools, external source files, or third-party Python packages are used.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import comb, gcd, lcm
import hashlib
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parents[1]

def add(*ps):
    z = {}
    for p in ps:
        for k, c in p.items():
            z[k] = z.get(k, 0) + c
    return {k: c for k, c in z.items() if c}

def scale(p, c):
    return {k: c*v for k, v in p.items() if c*v}

def mul(*ps):
    z = {(0, 0): 1}
    for p in ps:
        w = {}
        for (i, j), a in z.items():
            for (k, h), b in p.items():
                key = i+k, j+h
                w[key] = w.get(key, 0) + a*b
        z = {k: v for k, v in w.items() if v}
    return z

def power(p, n):
    z = {(0, 0): 1}
    for _ in range(n):
        z = mul(z, p)
    return z

def sub(p, q):
    return add(p, scale(q, -1))

one = {(0, 0): 1}
t = {(1, 0): 1}
b = {(0, 1): 1}

def diff(p, axis):
    z = {}
    for k, c in p.items():
        if k[axis]:
            h = list(k)
            h[axis] -= 1
            z[tuple(h)] = c*k[axis]
    return z

def ev(p, x, y):
    return sum(c*x**i*y**j for (i, j), c in p.items())

def at_b(p, y):
    z = {}
    for (i, j), c in p.items():
        z[i, 0] = z.get((i, 0), 0)+c*y**j
    return {k: v for k, v in z.items() if v}

def at_t(p, x):
    z = {}
    for (i, j), c in p.items():
        z[j, 0] = z.get((j, 0), 0)+c*x**i
    return {k: v for k, v in z.items() if v}

def integerize(p):
    den = lcm(*(F(v).denominator for v in p.values())) if p else 1
    return {k: int(v*den) for k, v in p.items()}, den

def dense(p):
    if not p:
        return []
    return [[p.get((i, j), 0) for i in range(max((i for i, h in p if h == j), default=0)+1)]
            for j in range(max(j for i, j in p)+1)]

def rational(q):
    q = F(q)
    return [q.numerator, q.denominator]

def box_json(box):
    return [rational(v) for v in box]

S = add(one, scale(t, 3))
E2 = scale(mul(t, sub(one, t)), -2)
C = mul(t, sub(sub(scale(one, 2), t), power(t, 2)))
pi = scale(mul(power(t, 2), power(sub(one, t), 2)), -1)
P = add(power(b, 6), scale(mul(E2, power(b, 5)), -1),
        mul(sub(mul(S, C), pi), power(b, 4)),
        mul(sub(sub(scale(mul(E2, pi), 2), power(C, 2)), mul(power(S, 2), pi)), power(b, 3)),
        mul(sub(mul(S, C, pi), power(pi, 2)), power(b, 2)),
        scale(mul(E2, power(pi, 2), b), -1), power(pi, 3))
Pb = diff(P, 1)
d = scale(sub(power(b, 2), pi), 2)
A = mul(b, sub(mul(b, S), C))
J = sub(scale(A, 2), mul(S, d))
H = sub(scale(A, 4), mul(S, d))
K = sub(pi, power(b, 2))
U = sub(sub(sub(scale(power(A, 2), 4), mul(b, power(d, 2))),
            scale(mul(t, A, d), 4)), scale(mul(t, power(d, 2)), 2))
V = add(scale(mul(A, b), -2), mul(sub(scale(mul(t, b), 2), mul(power(t, 2), sub(one, t))), d))
L = add(scale(mul(A, H, b), 2), mul(K, power(d, 2)))
NN = add(mul(power(U, 2), b), scale(mul(U, V, A), 2), mul(power(V, 2), power(d, 2)))
HH = add(mul(power(H, 2), power(b, 3)), scale(mul(H, K, A, b), 2), mul(power(K, 2), power(d, 2)))
CPOS = sub(mul(b, power(d, 2)), power(A, 2))
REALF = sub(add(mul(U, L, b), mul(sub(mul(V, L), mul(U, H, power(b, 2))), A)),
            mul(V, H, power(b, 2), power(d, 2)))
Q = {(i, 0): v for i, v in enumerate([32, 971, 989, 4800, 120])}

def divide_curve(f):
    r, q = dict(f), {}
    while r and max(j for i, j in r) >= 6:
        j = max(j for i, j in r)
        lead = {(i, j-6): c for (i, h), c in r.items() if h == j}
        q = add(q, lead)
        r = sub(r, mul(lead, P))
    return q, r

def reduced(raw):
    raw, den = integerize(raw)
    quo, rem = divide_curve(raw)
    g = gcd(*(abs(c) for c in rem.values())) if rem else 1
    rem = scale(rem, F(1, g))
    k = min((i for i, j in rem), default=0)
    rem = {(i-k, j): c*(-1)**k for (i, j), c in rem.items()}
    h = 0
    while rem:
        at_one = {}
        for (i, j), c in rem.items():
            at_one[j] = at_one.get(j, 0)+c
        if any(at_one.values()):
            break
        q, r = {}, dict(rem)
        while r and max(i for i, j in r) > 0:
            degree = max(i for i, j in r)
            lead = {(degree-1, j): -c for (i, j), c in r.items() if i == degree}
            q = add(q, lead)
            r = sub(r, mul(lead, sub(one, t)))
        assert not r
        rem = q
        h += 1
    return rem, dict(raw=dense(raw), quotient=dense(quo),
                    content=g, rational_denominator=den, positive_factor=dict(negative_t_power=k, one_minus_t_power=h))

@lru_cache(maxsize=20000)
def transform(n, lo, hi):
    den = lcm(lo.denominator, hi.denominator)
    low, high = int(lo*den), int(hi*den)
    return [[den**(n-i)*sum(comb(i, r)*low**(i-r)*high**r*comb(n-i, k-r)
                          for r in range(max(0, k-(n-i)), min(i, k)+1))
             for i in range(n+1)] for k in range(n+1)]

def bernstein(p, box, stats=None, label=None):
    p, _ = integerize(p)
    n = max((i for i, j in p), default=0)
    m = max((j for i, j in p), default=0)
    tl, tu, bl, bu = box
    tx, by = transform(n, tl, tu), transform(m, bl, bu)
    tmp = [[sum(c*tx[k][i] for (i, h), c in p.items() if h == j)
            for j in range(m+1)] for k in range(n+1)]
    co = [sum(tmp[k][j]*by[h][j] for j in range(m+1))
          for k in range(n+1) for h in range(m+1)]
    if stats is not None:
        rec = stats.setdefault(label, dict(checks=0, coefficients=0, max_t_degree=0,
            max_b_degree=0, max_coefficient_bits=0, integer_mul_add_pairs=0,
            min_relative_coefficient=None))
        rec['checks'] += 1
        rec['coefficients'] += len(co)
        rec['max_t_degree'] = max(rec['max_t_degree'], n)
        rec['max_b_degree'] = max(rec['max_b_degree'], m)
        rec['max_coefficient_bits'] = max(rec['max_coefficient_bits'], max(abs(int(v)).bit_length() for v in co))
        rec['integer_mul_add_pairs'] += (n+1)*len(p)+(n+1)*(m+1)**2
        normalized = [F(co[k*(m+1)+h], comb(n, k)*comb(m, h))
                      for k in range(n+1) for h in range(m+1)]
        ratio = min(normalized)/max(normalized) if min(co) > 0 else F(0)
        if rec['min_relative_coefficient'] is None or ratio < F(*rec['min_relative_coefficient']):
            rec['min_relative_coefficient'] = rational(ratio)
    return all(v > 0 for v in co)

@lru_cache(maxsize=50000)
def root(x):
    """Bisection is discovery only; the checker certifies every resulting strip."""
    pp = at_t(P, x)
    lo, hi = F(0), F(1)
    while ev(pp, hi, 0) <= 0:
        hi *= 2
    for _ in range(52):
        mid = (lo+hi)/2
        if ev(pp, mid, 0) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi

def candidate(lo, hi):
    ends = [root(lo), root(hi), root((lo+hi)/2)]
    low, high = min(v[0] for v in ends), max(v[1] for v in ends)
    pad = max((high-low)/8, high/F(1000000))
    # Dyadic rounding keeps the literal and transform sizes small.
    unit = F(1, 2**24)
    bl = ((low-pad)//unit)*unit
    bu = -((-(high+pad))//unit)*unit
    return lo, hi, max(unit, bl), bu

def branch_ok(box):
    tl, tu, bl, bu = box
    return (bernstein(Pb, box) and
            bernstein(scale(at_b(P, bl), -1), (tl, tu, F(0), F(0))) and
            bernstein(at_b(P, bu), (tl, tu, F(0), F(0))))

def partition(lo, hi, conds, depth=0):
    if depth > 28:
        raise RuntimeError(('subdivision limit', str(lo), str(hi)))
    bx = candidate(lo, hi)
    if branch_ok(bx) and all(bernstein(p, bx) for p in conds.values()):
        return [bx]
    mid = (lo+hi)/2
    return partition(lo, mid, conds, depth+1)+partition(mid, hi, conds, depth+1)

def isolate_q(lo, hi):
    lo, hi = F(lo), F(hi)
    sl = ev(Q, lo, 0)
    assert sl*ev(Q, hi, 0) < 0
    while hi-lo > F(1, 2**32):
        mid = (lo+hi)/2
        if sl*ev(Q, mid, 0) > 0:
            lo = mid
        else:
            hi = mid
    return lo, hi

def det(matrix):
    """Subset determinant over Z[t]; no division or symbolic algebra package."""
    n = len(matrix)
    dp = {0: one}
    for mask in range(1, 1 << n):
        row = mask.bit_count()-1
        val = {}
        for j in range(n):
            if mask >> j & 1:
                sign = -1 if (row+(mask & ((1 << j)-1)).bit_count()) % 2 else 1
                val = add(val, scale(mul(dp[mask ^ (1 << j)], matrix[row][j]), sign))
        dp[mask] = val
    return dp[(1 << n)-1]

def bezout():
    # D(z), with U degree <=2, V degree <=3, columns U*D and V*D'.
    D = [one, scale(S, -1), E2, scale(C, -1), pi]
    Dz = [scale(D[i], i) for i in range(1, 5)]
    cols = [[{}]*k + D + [{}]*(2-k) for k in range(3)]
    cols += [[{}]*k + Dz + [{}]*(3-k) for k in range(4)]
    mat = [[cols[j][i] for j in range(7)] for i in range(7)]
    delta = det(mat)
    cof = []
    for j in range(7):
        minor = [[mat[r][c] for c in range(7) if c != j] for r in range(1, 7)]
        cof.append(scale(det(minor), (-1)**j))
    return dict(U=[dense(p)[0] if p else [] for p in cof[:3]],
                V=[dense(p)[0] if p else [] for p in cof[3:]],
                rhs=dense(delta)[0],
                discriminant=dense(mul(power(t, 3), power(sub(t, one), 3), Q))[0],
                kind='sylvester-scaled-discriminant')

def tail(q, weights, n):
    total = F(0)
    for j, w in enumerate(weights):
        k = max(0, n+2-j)
        total += w*q**k*(k+1-k*q)/(1-q)**2
    return total

def conditions(q, m, weights):
    g1 = add(scale(power(b, 2), q*q), pi)
    raw = dict(G1=g1,
        G2=sub(mul(power(g1, 2), power(d, 2)), scale(mul(power(b, 3), power(J, 2)), q*q)),
        AMP=sub(mul(b, NN), scale(mul(power(d, 2), HH), m*m)),
        W1=sub(scale(b, weights[1]**2), scale(power(t, 2), 4)),
        W2=sub(scale(power(b, 2), weights[2]**2), scale(power(t, 2), 4)),
        W3=sub(scale(power(b, 3), weights[3]**2), mul(power(t, 4), power(sub(one, t), 2))),
        WIND=add(mul(U, H, power(b, 2)), mul(V, L)))
    ps, witnesses = {}, {}
    for name, f in raw.items():
        ps[name], witnesses[name] = reduced(f)
    return ps, witnesses

def rows_prefix(limit):
    D = [one, scale(S, -1), E2, scale(C, -1), pi]
    N = [one, scale(t, -2), scale(t, -2), scale(mul(power(t, 2), sub(one, t)), -1)]
    rows = []
    for n in range(limit):
        row = N[n] if n < 4 else {}
        for k in range(1, min(4, n)+1):
            row = sub(row, mul(D[k], rows[n-k]))
        rows.append(row)
    return rows

def row_sign(coeff, x):
    num, den = x.numerator, x.denominator
    value, dp = coeff[-1], den
    for c in reversed(coeff[:-1]):
        value = value*num+c*dp
        dp *= den
    return (value > 0)-(value < 0)

def sign_grids(rows):
    """Find exact interlacing separators; only the resulting sign grids are trusted."""
    previous_roots, previous = [], [1]
    grids = []
    for n, pp in enumerate(rows[1:], 1):
        coeff = dense(pp)[0]
        for attempt in range(128):
            pts = [(lo+hi)/2 for lo, hi in previous_roots]
            left = min(F(-1), previous_roots[0][0]*2) if previous_roots else F(-2)
            while row_sign(coeff, left) != (-1)**n:
                left *= 2
            grid = [left]+pts+[F(0)]
            if all(row_sign(coeff, x) == (-1)**(n-i) for i, x in enumerate(grid)):
                break
            refined = []
            for lo, hi in previous_roots:
                mid = (lo+hi)/2
                if row_sign(previous, lo)*row_sign(previous, mid) < 0:
                    hi = mid
                else:
                    lo = mid
                refined.append((lo, hi))
            previous_roots = refined
        else:
            raise RuntimeError(('sign grid discovery', n))
        grids.append(dict(n=n, points=[rational(v) for v in grid]))
        roots = []
        for lo, hi in zip(grid, grid[1:]):
            sign = row_sign(coeff, lo)
            while hi-lo > F(1, 2**16):
                mid = (lo+hi)/2
                sm = row_sign(coeff, mid)
                if sm == 0:
                    # Keep a strict rational bracket around an exact dyadic root.
                    width = min((hi-lo)/4, F(1, 2**18))
                    lo, hi = mid-width, mid+width
                    break
                if sm == sign:
                    lo = mid
                else:
                    hi = mid
            unit = F(1, 2**20)
            low = (lo//unit-1)*unit
            high = (-((-hi)//unit)+1)*unit
            assert row_sign(coeff, low)*row_sign(coeff, high) < 0
            lo, hi = low, high
            roots.append((lo, hi))
        previous_roots, previous = roots, coeff
    return grids

def q_gap_boxes(lo, hi, depth=0):
    bx = (lo, hi, F(0), F(0))
    if bernstein(scale(Q, -1), bx):
        return [[rational(lo), rational(hi)]]
    assert depth < 50
    mid = (lo+hi)/2
    return q_gap_boxes(lo, mid, depth+1)+q_gap_boxes(mid, hi, depth+1)

def produce(tag, q, m, be, endpoints, bz):
    started = time.monotonic()
    ps, witnesses = conditions(q, m, be)
    lo, hi = endpoints[0][0], endpoints[1][1]
    boxes = partition(lo, hi, ps)
    stats = {}
    for bx in boxes:
        tl, tu, bl, bu = bx
        assert bernstein(Pb, bx, stats, 'branch_derivative')
        assert bernstein(scale(at_b(P, bl), -1), (tl, tu, F(0), F(0)), stats, 'branch_lower_wall')
        assert bernstein(at_b(P, bu), (tl, tu, F(0), F(0)), stats, 'branch_upper_wall')
        for name, p in ps.items():
            assert bernstein(p, bx, stats, name)
    for left, right in zip(boxes, boxes[1:]):
        at = left[1]
        assert bernstein(at_t(Pb, at), (min(left[2], right[2]), max(left[3], right[3]), F(0), F(0)),
                         stats, 'branch_junction')
    ep = []
    cpos, cpos_wit = reduced(CPOS)
    rf, rf_wit = reduced(REALF)
    for index, (el, eu) in enumerate(endpoints):
        # Certified endpoint strip, and signs just inside/outside the collision.
        bx = candidate(el, eu)
        assert branch_ok(bx)
        assert bernstein(Pb, bx, stats, 'endpoint_simple')
        asign = -1 if index == 0 else 1
        assert bernstein(scale(A, asign), bx, stats, 'endpoint_a')
        assert bernstein(scale(rf, asign), bx, stats, 'endpoint_F')
        side_boxes = []
        for ts, sign in [(el, -1 if index == 0 else 1), (eu, 1 if index == 0 else -1)]:
            rl, ru = root(ts)
            tight = (ts, ts, rl, ru)
            assert branch_ok(tight)
            assert bernstein(scale(cpos, sign), tight, stats, 'endpoint_cpos_sides')
            side_boxes.append(dict(box=box_json(tight), sign=sign))
        qsign = 1 if ev(diff(Q, 0), el, 0) > 0 else -1
        assert bernstein(scale(diff(Q, 0), qsign), (el, eu, F(0), F(0)), stats, 'endpoint_Q_derivative')
        ep.append(dict(interval=[rational(el), rational(eu)], box=box_json(bx),
                       derivative_sign=qsign, a_sign=asign, F_sign=asign, cpos_sides=side_boxes))
    n0 = 0
    while tail(q, be, n0) >= m:
        n0 += 1
    rows = rows_prefix(n0)
    finite = dict(kind='sign-grids', rows_range=[1, n0-1],
        prefix_sign_grids=sign_grids(rows), status='exact_sign_grids',
        generated_rows=[dense(p)[0] for p in rows[1:]])
    cert = dict(schema='polytool.effective-bkw.v1', namespace='RealRooted.EffectiveBKW',
        family=dict(name='path-cube', representation='N/D',
            N=[dense(p)[0] if p else [] for p in [one, scale(t, -2), scale(t, -2),
               scale(mul(power(t, 2), sub(one, t)), -1)]],
            D=[dense(p)[0] if p else [] for p in [one, scale(S, -1), E2, scale(C, -1), pi]]),
        P2=dense(P), factorization_witness=factorization_witness(),
        endpoint_roots=dict(polynomial=dense(Q)[0], roots=ep,
                           negative_gap_boxes=q_gap_boxes(endpoints[0][1], endpoints[1][0])), discriminant_bezout=bz,
        branch=dict(domain=[rational(lo), rational(hi)], derivative_sign=1,
                    cells=[box_json(bx) for bx in boxes]),
        sign_conditions={name: dict(polynomial=dense(p), neg=False, reduction=witnesses[name],
                                   boxes=list(range(len(boxes)))) for name, p in ps.items()},
        endpoint_auxiliary=dict(CPOS=dict(polynomial=dense(cpos), reduction=cpos_wit),
                                REALF=dict(polynomial=dense(rf), reduction=rf_wit)),
        constants=dict(q=rational(q), m=rational(m), beta=[rational(v) for v in be], e=2, w=-1, sigma=0),
        N0=n0, tail_witness=dict(T_N0=rational(tail(q, be, n0)), T_previous=rational(tail(q, be, n0-1))),
        prefix=finite, exterior_sign_source=dict(kind='monic-degree-n',
             argument='matrix M0+t M1; (M1^n)[0,0]=1; positive row coefficients'),
        lean_replay='not_attempted', metrics=dict(conditions=stats, branch_cells=len(boxes),
            generation_seconds='not recorded (deterministic output)'))
    # Ensure all polynomial literal values are integers, even when normalized by a Fraction.
    def clean(v):
        if isinstance(v, F):
            assert v.denominator == 1
            return v.numerator
        if isinstance(v, dict):
            return {k: clean(w) for k, w in v.items()}
        if isinstance(v, list):
            return [clean(w) for w in v]
        return v
    cert = clean(cert)
    return cert

def factorization_witness():
    # Cleared coefficients of (x²-2ax+b)(x²+c1*x+c0)-p(x).
    raw = [add(mul(power(b, 2), J), scale(mul(A, pi), -2), mul(C, b, d)),
           sub(add(mul(b, power(d, 2), b), mul(pi, power(d, 2)), scale(mul(A, J, b), -2)),
               mul(E2, b, power(d, 2))),
           sub(J, sub(scale(A, 2), mul(S, d)))]
    result = []
    for f in raw:
        q, r = divide_curve(f)
        assert not r, ('factorization', dense(r))
        result.append(dict(raw=dense(f), quotient=dense(q)))
    return dict(denominator_a=dense(d), numerator_a=dense(A), identities=result)

# Independent exact replay, from the Phase 0 checker.
import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import comb, lcm
import json
from pathlib import Path
import sys
import time

if not __debug__:
    raise RuntimeError('assertions must be enabled')
replay_F = Fraction

class replay_Poly:
    def __init__(self, terms=None):
        self.c = {k: replay_F(v) for k, v in (terms or {}).items() if v}

    @staticmethod
    def cast(v):
        return v if isinstance(v, replay_Poly) else replay_Poly({(0, 0): v})

    def __add__(self, v):
        if not isinstance(v, (replay_Poly, int, replay_F)):
            return NotImplemented
        v = self.cast(v)
        z = dict(self.c)
        for k, x in v.c.items():
            z[k] = z.get(k, 0)+x
        return replay_Poly(z)
    __radd__ = __add__

    def __neg__(self):
        return replay_Poly({k: -v for k, v in self.c.items()})

    def __sub__(self, v):
        if not isinstance(v, (replay_Poly, int, replay_F)):
            return NotImplemented
        return self+-self.cast(v)

    def __rsub__(self, v):
        return self.cast(v)+-self

    def __mul__(self, v):
        if not isinstance(v, (replay_Poly, int, replay_F)):
            return NotImplemented
        v = self.cast(v)
        if 'replay_COUNTS' in globals():
            replay_COUNTS['identity_coefficient_mul_add_pairs'] += len(self.c)*len(v.c)
        z = {}
        for (i, j), x in self.c.items():
            for (k, h), y in v.c.items():
                at = i+k, j+h
                z[at] = z.get(at, 0)+x*y
        return replay_Poly(z)
    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out, p = replay_Poly.cast(1), self
        while n:
            if n % 2:
                out *= p
            p *= p
            n //= 2
        return out

    def __eq__(self, v):
        return self.c == self.cast(v).c

    def derivative(self, axis):
        out = {}
        for k, c in self.c.items():
            if k[axis]:
                at = list(k)
                at[axis] -= 1
                out[tuple(at)] = c*k[axis]
        return replay_Poly(out)

    def evaluate(self, x, y):
        return sum(v*x**i*y**j for (i, j), v in self.c.items())

    def specialize(self, axis, value):
        z = {}
        for (i, j), c in self.c.items():
            at, fac = ((i, 0), value**j) if axis == 1 else ((j, 0), value**i)
            z[at] = z.get(at, 0)+c*fac
        return replay_Poly(z)

replay_T = replay_Poly({(1, 0): 1})
replay_B = replay_Poly({(0, 1): 1})
replay_S = 1+3*replay_T
replay_E = -2*replay_T*(1-replay_T)
replay_C = replay_T*(2-replay_T-replay_T**2)
replay_PI = -replay_T**2*(1-replay_T)**2
replay_DEN = 2*(replay_B**2-replay_PI)
replay_ANUM = replay_B*(replay_B*replay_S-replay_C)
replay_EXPECTED_P = (replay_B**6-replay_E*replay_B**5+(replay_S*replay_C-replay_PI)*replay_B**4+(2*replay_E*replay_PI-replay_C**2-replay_S**2*replay_PI)*replay_B**3
              +(replay_S*replay_C*replay_PI-replay_PI**2)*replay_B**2-replay_E*replay_PI**2*replay_B+replay_PI**3)
replay_Q = 32+971*replay_T+989*replay_T**2+4800*replay_T**3+120*replay_T**4

class replay_Rat:
    """Denominator b^i DEN^j, positive on every certified branch strip."""
    def __init__(self, numerator, i=0, j=0):
        self.num, self.i, self.j = replay_Poly.cast(numerator), i, j

    @staticmethod
    def cast(v):
        return v if isinstance(v, replay_Rat) else replay_Rat(v)

    def __add__(self, other):
        other = self.cast(other)
        i, j = max(self.i, other.i), max(self.j, other.j)
        return replay_Rat(self.num*replay_B**(i-self.i)*replay_DEN**(j-self.j)
                   +other.num*replay_B**(i-other.i)*replay_DEN**(j-other.j), i, j)
    __radd__ = __add__

    def __neg__(self):
        return replay_Rat(-self.num, self.i, self.j)

    def __sub__(self, v):
        return self+-self.cast(v)

    def __rsub__(self, v):
        return self.cast(v)+-self

    def __mul__(self, v):
        v = self.cast(v)
        return replay_Rat(self.num*v.num, self.i+v.i, self.j+v.j)
    __rmul__ = __mul__

    def __pow__(self, n):
        return replay_Rat(self.num**n, self.i*n, self.j*n)

def replay_qnum(pair):
    assert isinstance(pair, list) and len(pair) == 2
    assert all(type(v) is int for v in pair) and pair[1] > 0
    q = replay_F(*pair)
    assert [q.numerator, q.denominator] == pair
    return q

def replay_polynomial(lists):
    assert isinstance(lists, list)
    assert all(isinstance(row, list) for row in lists)
    assert all(type(v) is int for row in lists for v in row)
    return replay_Poly({(i, j): v for j, row in enumerate(lists) for i, v in enumerate(row)})

def replay_univariate(row):
    return replay_polynomial([row])

def replay_box(data):
    assert len(data) == 4
    tl, tu, bl, bu = map(replay_qnum, data)
    assert tl <= tu and bl <= bu
    return tl, tu, bl, bu

@lru_cache(maxsize=12000)
def replay_taylor_weights(n, lo, hi):
    den = lcm(lo.denominator, hi.denominator)
    a, step = int(lo*den), int((hi-lo)*den)
    # First Taylor-shift p(lo+(hi-lo)*s), then Bernstein power conversion.
    out = []
    terms = sum(min(i, k)+1 for i in range(n+1) for k in range(n+1))
    replay_COUNTS['basis_cached_matrices'] += 1
    replay_COUNTS['basis_integer_products_estimate'] += 3*terms+(n+1)**2+3*n
    replay_COUNTS['basis_integer_additions_estimate'] += terms-(n+1)**2
    for k in range(n+1):
        out.append([den**(n-i)*sum(comb(i, r)*a**(i-r)*step**r*comb(n-r, k-r)
                    for r in range(min(i, k)+1)) for i in range(n+1)])
    return out

replay_COUNTS = dict(bernstein_checks=0, coefficient_sign_checks=0, max_t_degree=0,
              max_b_degree=0, max_coefficient_bits=0, integer_mul_add_pairs=0,
              identity_coefficient_mul_add_pairs=0, basis_cached_matrices=0,
              basis_integer_products_estimate=0, basis_integer_additions_estimate=0)

def replay_positive(p, bx):
    a, z, c, d = bx
    nt = max((i for i, j in p.c), default=0)
    nb = max((j for i, j in p.c), default=0)
    wx, wy = replay_taylor_weights(nt, a, z), replay_taylor_weights(nb, c, d)
    den = lcm(*(v.denominator for v in p.c.values())) if p.c else 1
    pp = {k: int(v*den) for k, v in p.c.items()}
    shifted = [[sum(v*wx[k][i] for (i, h), v in pp.items() if h == j)
                for j in range(nb+1)] for k in range(nt+1)]
    values = [sum(shifted[i][j]*wy[k][j] for j in range(nb+1))
              for i in range(nt+1) for k in range(nb+1)]
    assert all(v > 0 for v in values), ('Bernstein positivity failed', bx)
    replay_COUNTS['bernstein_checks'] += 1
    replay_COUNTS['coefficient_sign_checks'] += len(values)
    replay_COUNTS['max_t_degree'] = max(replay_COUNTS['max_t_degree'], nt)
    replay_COUNTS['max_b_degree'] = max(replay_COUNTS['max_b_degree'], nb)
    replay_COUNTS['max_coefficient_bits'] = max(replay_COUNTS['max_coefficient_bits'], max(abs(v).bit_length() for v in values))
    replay_COUNTS['integer_mul_add_pairs'] += (nt+1)*len(pp)+(nt+1)*(nb+1)**2

def replay_strip(curve, bx):
    a, z, lo, hi = bx
    assert a <= z and 0 < lo < hi
    replay_positive(curve.derivative(1), bx)
    replay_positive(-curve.specialize(1, lo), (a, z, replay_F(0), replay_F(0)))
    replay_positive(curve.specialize(1, hi), (a, z, replay_F(0), replay_F(0)))

def replay_glued(curve, cells):
    assert cells
    for bx in cells:
        assert bx[0] < bx[1]
        replay_strip(curve, bx)
    for left, right in zip(cells, cells[1:]):
        assert left[1] == right[0]
        replay_positive(curve.derivative(1).specialize(0, left[1]),
                 (min(left[2], right[2]), max(left[3], right[3]), replay_F(0), replay_F(0)))

def replay_condition_expressions(q, m, beta):
    a, c0 = replay_Rat(replay_ANUM, 0, 1), replay_Rat(replay_PI, 1, 0)
    c1 = 2*a-replay_S
    # Reduction mod lambda²-2a*lambda+b, using independently constructed rational functions.
    un, vn = 4*a**2-replay_B-4*replay_T*a-2*replay_T, -2*a*replay_B+2*replay_T*replay_B-replay_T**2*(1-replay_T)
    uh, vh = 2*a+c1, c0-replay_B
    ud, vd = 2*a*uh+vh, -uh*replay_B
    def norm(u, v):
        return u**2*replay_B+2*u*v*a+v**2
    def real_product(u, v, r, s):
        return u*r*replay_B+(u*s+v*r)*a+v*s
    return dict(G1=q*q*replay_B+c0, G2=(q*q*replay_B+c0)**2-q*q*replay_B*c1**2,
        AMP=norm(un, vn)-m*m*replay_B*norm(uh, vh),
        W1=replay_Rat(beta[1]**2*replay_B-4*replay_T**2), W2=replay_Rat(beta[2]**2*replay_B**2-4*replay_T**2),
        W3=replay_Rat(beta[3]**2*replay_B**3-replay_T**4*(1-replay_T)**2), WIND=-(un*vd-vn*ud),
        CPOS=replay_B-a**2, REALF=real_product(un, vn, ud, vd))

replay_DENOM_POWERS = dict(G1=(1, 0), G2=(2, 2), AMP=(1, 4), W1=(0, 0),
                    W2=(0, 0), W3=(0, 0), WIND=(1, 3), CPOS=(0, 2), REALF=(1, 4))

def replay_reduction(name, entry, expression, curve):
    p = replay_polynomial(entry['polynomial'])
    wit = entry['reduction']
    raw, quo = replay_polynomial(wit['raw']), replay_polynomial(wit['quotient'])
    assert type(wit['content']) is int and wit['content'] > 0
    assert type(wit['rational_denominator']) is int and wit['rational_denominator'] > 0
    factors = wit['positive_factor']
    k, h = factors['negative_t_power'], factors['one_minus_t_power']
    assert type(k) is int and type(h) is int and 0 <= k <= 40 and 0 <= h <= 40
    assert raw == wit['content']*(-replay_T)**k*(1-replay_T)**h*p+curve*quo, ('reduction identity', name)
    i, j = replay_DENOM_POWERS[name]
    expr = replay_Rat.cast(expression)
    assert expr.num*replay_B**i*replay_DEN**j*wit['rational_denominator'] == raw*replay_B**expr.i*replay_DEN**expr.j, ('expression identity', name)
    assert max((j for i, j in p.c), default=0) < 6
    return p

def replay_determinant(m):
    n = len(m)
    ans = replay_Poly()
    for perm in permutations(range(n)):
        term = replay_Poly.cast((-1)**sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n)))
        for i, j in enumerate(perm):
            term *= m[i][j]
        ans += term
    return ans

def replay_check_family(data):
    assert data['name'] == 'path-cube' and data['representation'] == 'N/D'
    N, D = list(map(replay_univariate, data['N'])), list(map(replay_univariate, data['D']))
    assert N == [replay_Poly.cast(1), -2*replay_T, -2*replay_T, -replay_T**2*(1-replay_T)]
    assert D == [replay_Poly.cast(1), -replay_S, replay_E, -replay_C, replay_PI]
    matrix = [[1+replay_T, 2*replay_T, 0, 0], [1, replay_T, 2+replay_T, 3*replay_T], [1, replay_T, 0, 0], [0, 0, 1, replay_T]]
    mat = [[(1 if i == j else 0)-replay_B*matrix[i][j] for j in range(4)] for i in range(4)]
    assert replay_determinant(mat) == sum((v*replay_B**j for j, v in enumerate(D)), replay_Poly())
    assert replay_determinant([row[1:] for row in mat[1:]]) == sum((v*replay_B**j for j, v in enumerate(N)), replay_Poly())
    # M1 e1=e1 gives the monic degree law for every n; M0,M1 >=0.
    for i, row in enumerate(matrix):
        for j, value in enumerate(row):
            p = replay_Poly.cast(value)
            assert all(v >= 0 and k in [(0, 0), (1, 0)] for k, v in p.c.items())
            if j == 0:
                assert p.c.get((1, 0), 0) == (1 if i == 0 else 0)
    return N, D

def replay_check_factorization(wit, curve):
    assert replay_polynomial(wit['denominator_a']) == replay_DEN
    assert replay_polynomial(wit['numerator_a']) == replay_ANUM
    J = 2*replay_ANUM-replay_S*replay_DEN
    expected = [replay_B**2*J-2*replay_ANUM*replay_PI+replay_C*replay_B*replay_DEN,
                replay_B**2*replay_DEN**2+replay_PI*replay_DEN**2-2*replay_ANUM*J*replay_B-replay_E*replay_B*replay_DEN**2,
                J-(2*replay_ANUM-replay_S*replay_DEN)]
    assert len(wit['identities']) == 3
    for identity, raw in zip(wit['identities'], expected):
        assert replay_polynomial(identity['raw']) == raw
        assert raw == curve*replay_polynomial(identity['quotient'])

def replay_check_discriminant(wit, D):
    u, v = list(map(replay_univariate, wit['U'])), list(map(replay_univariate, wit['V']))
    assert len(u) == 3 and len(v) == 4
    out = [replay_Poly() for _ in range(7)]
    for i, f in enumerate(u):
        for j, p in enumerate(D):
            out[i+j] += f*p
    for i, f in enumerate(v):
        for j in range(1, len(D)):
            out[i+j-1] += f*j*D[j]
    rhs = replay_univariate(wit['rhs'])
    assert out[0] == rhs and all(p == 0 for p in out[1:]), 'Bezout identity'
    disc = replay_T**3*(replay_T-1)**3*replay_Q
    assert replay_univariate(wit['discriminant']) == disc, 'discriminant literal'
    assert rhs == replay_PI*disc or rhs == -replay_PI*disc, 'scaled discriminant RHS'

def replay_contained(bx, parent):
    return parent[0] <= bx[0] <= bx[1] <= parent[1] and parent[2] <= bx[2] < bx[3] <= parent[3]

def replay_check_endpoints(data, curve, cells, aux):
    assert replay_univariate(data['polynomial']) == replay_Q
    roots = data['roots']
    assert len(roots) == 2
    spans = []
    for i, entry in enumerate(roots):
        lo, hi = map(replay_qnum, entry['interval'])
        assert lo < hi < 0 and replay_Q.evaluate(lo, 0)*replay_Q.evaluate(hi, 0) < 0
        sign = entry['derivative_sign']
        assert sign in [-1, 1]
        replay_positive(sign*replay_Q.derivative(0), (lo, hi, replay_F(0), replay_F(0)))
        ep = replay_box(entry['box'])
        assert ep[:2] == (lo, hi)
        replay_strip(curve, ep)
        assert any(replay_contained(ep, parent) for parent in cells), 'endpoint branch identification'
        sign = -1 if i == 0 else 1
        assert entry['a_sign'] == entry['F_sign'] == sign
        replay_positive(sign*replay_ANUM, ep)
        replay_positive(sign*aux['REALF'], ep)
        sides = entry['cpos_sides']
        assert len(sides) == 2
        for j, item in enumerate(sides):
            bx = replay_box(item['box'])
            assert bx[0] == bx[1] == [lo, hi][j]
            assert replay_contained(bx, ep)
            replay_strip(curve, bx)
            wanted = [-1, 1][j] if i == 0 else [1, -1][j]
            assert item['sign'] == wanted
            replay_positive(wanted*aux['CPOS'], bx)
        spans.append((lo, hi))
    assert cells[0][0] == spans[0][0] and cells[-1][1] == spans[1][1]
    gaps = [tuple(map(replay_qnum, bx)) for bx in data['negative_gap_boxes']]
    assert gaps and gaps[0][0] == spans[0][1] and gaps[-1][1] == spans[1][0]
    for i, (a, z) in enumerate(gaps):
        assert a < z
        if i:
            assert gaps[i-1][1] == a
        replay_positive(-replay_Q, (a, z, replay_F(0), replay_F(0)))

def replay_tail(q, beta, n):
    # Compute total series minus its finite prefix, independently of producer's tail formula.
    out = replay_F(0)
    for j, w in enumerate(beta):
        k = max(0, n+2-j)
        out += w*(1/(1-q)**2-sum((h+1)*q**h for h in range(k)))
    return out

def replay_prefix(data, N, D, n0):
    assert data['rows_range'] == [1, n0-1]
    rows = [replay_Poly.cast(1)]
    for n in range(1, n0):
        p = N[n] if n < len(N) else replay_Poly()
        for j in range(1, min(n, len(D)-1)+1):
            p -= D[j]*rows[n-j]
        rows.append(p)
    assert list(map(replay_univariate, data['generated_rows'])) == rows[1:]
    assert len(data['prefix_sign_grids']) == n0-1
    evaluations, bits = 0, 0
    for n, (p, entry) in enumerate(zip(rows[1:], data['prefix_sign_grids']), 1):
        assert entry['n'] == n
        assert p.c.get((n, 0)) == 1 and max(i for i, j in p.c) == n
        assert all(v > 0 for v in p.c.values())
        pts = list(map(replay_qnum, entry['points']))
        assert len(pts) == n+1 and all(a < z for a, z in zip(pts, pts[1:]))
        assert pts[-1] == 0
        coeff = [int(p.c.get((i, 0), 0)) for i in range(n+1)]
        for i, x in enumerate(pts):
            # Integer homogenized Horner, independently evaluated from JSON.
            num, den = x.numerator, x.denominator
            value, power = 0, 1
            for c in reversed(coeff):
                value = value*num+c*power
                power *= den
            assert (-1)**(n-i)*value > 0, ('prefix sign', n, i)
            evaluations += 1
            bits = max(bits, abs(value).bit_length())
    return dict(rows=n0-1, grid_evaluations=evaluations, max_grid_value_bits=bits)

def replay_verify(cert):
    assert cert['schema'] == 'polytool.effective-bkw.v1'
    assert cert['namespace'] == 'RealRooted.EffectiveBKW'
    N, D = replay_check_family(cert['family'])
    curve = replay_polynomial(cert['P2'])
    assert curve == replay_EXPECTED_P
    replay_check_factorization(cert['factorization_witness'], curve)
    replay_check_discriminant(cert['discriminant_bezout'], D)
    constants = cert['constants']
    q, m = replay_qnum(constants['q']), replay_qnum(constants['m'])
    beta = list(map(replay_qnum, constants['beta']))
    assert 0 < q < 1 and m > 0 and len(beta) == 4 and beta[0] >= 1 and all(w >= 0 for w in beta)
    assert constants['e'] == 2 and constants['w'] == -1 and constants['sigma'] == 0
    expressions = replay_condition_expressions(q, m, beta)
    branch = cert['branch']
    assert branch['derivative_sign'] == 1
    cells = [replay_box(bx) for bx in branch['cells']]
    domain = tuple(map(replay_qnum, branch['domain']))
    assert domain == (cells[0][0], cells[-1][1]) and domain[1] < 0
    replay_glued(curve, cells)
    entries = cert['sign_conditions']
    assert set(entries) == set(expressions)-{'CPOS', 'REALF'}
    for name, entry in entries.items():
        assert entry['neg'] is False
        p = replay_reduction(name, entry, expressions[name], curve)
        assert entry['boxes'] == list(range(len(cells))), ('condition coverage', name)
        for bx in cells:
            replay_positive(p, bx)
    aux = {name: replay_reduction(name, cert['endpoint_auxiliary'][name], expressions[name], curve)
           for name in ['CPOS', 'REALF']}
    replay_check_endpoints(cert['endpoint_roots'], curve, cells, aux)
    n0 = cert['N0']
    assert type(n0) is int and n0 > 0
    now, prev = replay_tail(q, beta, n0), replay_tail(q, beta, n0-1)
    assert now < m <= prev
    assert replay_qnum(cert['tail_witness']['T_N0']) == now and replay_qnum(cert['tail_witness']['T_previous']) == prev
    finite = replay_prefix(cert['prefix'], N, D, n0)
    assert cert['exterior_sign_source']['kind'] == 'monic-degree-n'
    return dict(status='verified', N0=n0, branch_cells=len(cells), conditions={k: len(v['boxes']) for k, v in entries.items()},
                endpoint_b_simple=True, finite=finite, cost=dict(replay_COUNTS), lean_replay='not_attempted')


# Lean rendering. All generated data are reproduced by `generate`; `check` compares
# bytes without writing. No result of Python replay is a premise of a Lean proof.
def lean_list(values, render=str, indent=2):
    items = [render(v) for v in values]
    short = '[' + ', '.join(items) + ']'
    if len(short) + indent <= 98 and '\n' not in short:
        return short
    return '[\n' + ',\n'.join(' ' * (indent + 2) + v for v in items) + '\n' + ' ' * indent + ']'


def lean_q(q):
    return '⟨' + str(q[0]) + ', ' + str(q[1]) + '⟩'


def lean_poly2(p):
    return lean_list(p, lambda row: lean_list(row, indent=4))


def lean_module(imports, description, body, exposed=False):
    return ('/- Generated by scripts/ebkw_pathcube_certificate.py. -/\nmodule\n\n' +
            '\n'.join(imports) + '\n\n/-!\n# ' + description + '\n-/\n\n' +
            ('@[expose] public section\n\n' if exposed else 'public section\n\n') +
            'namespace RealRooted.EffectiveBKW.PathCube\n\n' + body +
            '\nend RealRooted.EffectiveBKW.PathCube\n')


def declaration(name, typ, value, description):
    return f'/-- {description} -/\ndef {name} : {typ} :=\n  {value}\n\n'


def proof(name, statement, description):
    return f'/-- {description} -/\ntheorem {name} :\n    {statement} := by\n  decide +kernel\n\n'


def render_certificate(cert):
    out = {}
    data = declaration('curve', 'IntPoly2', lean_poly2(cert['P2']),
                       'The monic pair-product resolvent, ascending in b and then t.')
    for name, entry in cert['sign_conditions'].items():
        data += declaration('condition' + name, 'IntPoly2', lean_poly2(entry['polynomial']),
                            'Reduced polynomial for the ' + name + ' condition.')
    for i, bx in enumerate(cert['branch']['cells']):
        qs = list(map(lean_q, bx))
        value = '⟨' + ', '.join(qs) + '⟩'
        if len(value) > 96:
            value = '⟨\n    ' + ',\n    '.join(qs) + '\n  ⟩'
        data += declaration(f'cell{i:03}', 'BranchCell',
                            value,
                            f'Certified branch rectangle {i}.')
    names = [f'cell{i:03}' for i in range(len(cert['branch']['cells']))]
    block_names = []
    for start in range(0, len(names), 16):
        name = f'cellBlock{start // 16:02}'
        block_names.append(name)
        data += declaration(name, 'List BranchCell', lean_list(names[start:start + 16]),
                            'A short block of consecutive branch rectangles.')
    data += declaration('cells', 'List BranchCell', ' ++\n  '.join(block_names),
                        'Ordered partition of the rational hull of the phase interval.')
    lo, hi = cert['branch']['domain']
    data += declaration('branch', 'Branch',
                        f'⟨curve, cells, {lean_q(lo)}, {lean_q(hi)}, false⟩',
                        'The branch data; its check is a separate proof obligation.')
    out['CertificateData.lean'] = lean_module(
        ['public import RealRooted.EffectiveBKW.Certificate.Branch'],
        'Path-cube branch and sign data', data, True)
    for start in range(0, len(names), 60):
        body = ''
        for i in range(start, min(start + 60, len(names))):
            body += proof(f'cell{i:03}_compatible',
                          f'cells.all (fun c ↦ cell{i:03}.compatible c curve false) = true',
                          f'All overlap and disjointness checks for rectangle {i}.')
        out[f'Compatibility{start // 60:02}.lean'] = lean_module(
            ['public import RealRooted.EffectiveBKW.PathCube.CertificateData'],
            f'Path-cube overlap checks beginning at {start}', body)
    for start in range(0, len(names), 16):
        body = ''
        for i in range(start, min(start + 16, len(names))):
            name = names[i]
            body += proof(f'cell{i:03}_check', f'{name}.check curve false = true',
                          f'Kernel replay of branch rectangle {i}.')
            for cond in cert['sign_conditions']:
                body += proof(f'condition{cond}_{i:03}',
                              f'condition{cond}.posOnBox {name}.tlo {name}.thi '
                              f'{name}.lo {name}.hi = true',
                              f'Kernel replay of {cond} on rectangle {i}.')
        out[f'Boxes{start // 16:02}.lean'] = lean_module(
            ['public import RealRooted.EffectiveBKW.PathCube.CertificateData'],
            f'Path-cube box checks {start} through {min(start + 15, len(names) - 1)}', body)
    body = proof('cells_bounds',
                 'cells.all (fun c ↦ branch.lo.le c.tlo && c.thi.le branch.hi) = true',
                 'Each cell lies inside the prescribed rational hull.')
    body += proof('cells_cover', 'Branch.covers branch.lo branch.hi cells = true',
                  'Exact adjacency of the 169 rational parameter intervals.')
    body += proof('cells_lower_pos',
                  'cells.all (fun c ↦ (⟨0, 1⟩ : QNum).lt c.lo) = true',
                  'Every certified strip has a strictly positive lower wall.')
    out['BranchBounds.lean'] = lean_module(
        ['public import RealRooted.EffectiveBKW.PathCube.CertificateData'],
        'The rational hull and coverage of the path-cube cells', body)
    return out


def render_branch_facts(cert):
    """Assemble separately checked cells through short, predicate-generic blocks."""
    import textwrap
    count = len(cert['branch']['cells'])
    blocks = [f'cellBlock{i:02}' for i in range((count + 15) // 16)]
    body = ''
    for start in range(0, count, 16):
        block = blocks[start // 16]
        hypotheses = [f'h{i:03}' for i in range(start, min(start + 16, count))]
        body += ('/-- Assemble a short block without unfolding its predicate. -/\n'
                 f'private theorem {block}_all {{p : BranchCell → Bool}}\n')
        for i, h in enumerate(hypotheses, start):
            body += f'    ({h} : p cell{i:03} = true)\n'
        body += f'    : {block}.all p = true := by\n'
        args = [block, 'List.all_cons', 'List.all_nil'] + hypotheses + ['Bool.true_and']
        lines = textwrap.wrap(', '.join(args), width=92, break_long_words=False,
                              break_on_hyphens=False)
        body += '  simp only [\n    ' + '\n    '.join(lines) + ']\n\n'
    body += ('/-- Assemble block predicates without descending into their applications. -/\n'
             'private theorem cells_all {p : BranchCell → Bool}\n')
    hypotheses = [f'h{i:02}' for i in range(len(blocks))]
    for block, h in zip(blocks, hypotheses):
        body += f'    ({h} : {block}.all p = true)\n'
    body += '    : cells.all p = true := by\n'
    args = ['cells', 'List.all_append'] + hypotheses + ['Bool.true_and']
    lines = textwrap.wrap(', '.join(args), width=92, break_long_words=False,
                          break_on_hyphens=False)
    body += '  simp only [\n    ' + '\n    '.join(lines) + ']\n\n'

    def assembled(name, expression, checks, doc):
        result = f'/-- {doc} -/\ntheorem {name} :\n    {expression} = true := by\n'
        result += '  apply cells_all\n'
        for start in range(0, count, 16):
            application = blocks[start // 16] + '_all ' + ' '.join(checks[start:start + 16])
            lines = textwrap.wrap(application, width=90, break_long_words=False,
                                  break_on_hyphens=False)
            result += '  · exact ' + '\n      '.join(lines) + '\n'
        return result + '\n'

    body += assembled('cells_check', 'cells.all (fun c ↦ c.check curve false)',
                      [f'cell{i:03}_check' for i in range(count)],
                      'Assemble the separately checked branch rectangles.')
    body += assembled('cells_compatible',
                      'cells.all (fun c ↦ cells.all (fun d ↦ c.compatible d curve false))',
                      [f'cell{i:03}_compatible' for i in range(count)],
                      'Assemble the separately checked overlap rows.')
    for cond in cert['sign_conditions']:
        body += assembled(f'condition{cond}_checks',
                          f'cells.all (fun c ↦ condition{cond}.posOnBox c.tlo c.thi c.lo c.hi)',
                          [f'condition{cond}_{i:03}' for i in range(count)],
                          f'Assemble the separate box checks for {cond}.')
    body += '''/-- All hypotheses of the branch soundness theorem are checked. -/
theorem branch_check : branch.check = true := by
  have hcells : branch.cells.all (fun c ↦
      c.check branch.curve branch.neg && branch.lo.le c.tlo &&
        c.thi.le branch.hi) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    have hcheck := List.all_eq_true.mp cells_check c hc
    have hbounds := List.all_eq_true.mp cells_bounds c hc
    simp only [Bool.and_eq_true] at hbounds ⊢
    exact ⟨⟨hcheck, hbounds.1⟩, hbounds.2⟩
  simp only [Branch.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel⟩,
    cells_cover⟩, hcells⟩, cells_compatible⟩

/-- The certified resolvent branch is continuous on the entire rational hull. -/
theorem continuousOn_branch :
    ContinuousOn branch.y (Set.Icc branch.lo.val branch.hi.val) :=
  (Branch.check_sound branch_check).1

/-- The selected branch satisfies the resolvent equation everywhere. -/
theorem curve_eval_branch {t : ℝ} (ht : t ∈ Set.Icc branch.lo.val branch.hi.val) :
    curve.eval t (branch.y t) = 0 :=
  (Branch.check_sound branch_check).2.1 t ht

private theorem posOn_branch {f : IntPoly2}
    (h : cells.all (fun c ↦ f.posOnBox c.tlo c.thi c.lo c.hi) = true)
    {t : ℝ} (ht : t ∈ Set.Icc branch.lo.val branch.hi.val) :
    0 < f.eval t (branch.y t) := by
  obtain ⟨c, hc, htc⟩ := Branch.covers_sound cells_cover ht
  exact IntPoly2.posOnBox_sound (List.all_eq_true.mp h c hc) htc
    ((Branch.check_sound branch_check).2.2 c hc t htc)

'''
    for cond in cert['sign_conditions']:
        body += (f'/-- The {cond} reduced sign condition holds on the continuous branch. -/\n'
                 f'theorem condition{cond}_pos {{t : ℝ}}\n'
                 '    (ht : t ∈ Set.Icc branch.lo.val branch.hi.val) :\n'
                 f'    0 < condition{cond}.eval t (branch.y t) :=\n'
                 f'  posOn_branch condition{cond}_checks ht\n\n')
    imports = ['public import RealRooted.EffectiveBKW.PathCube.CertificateData',
               'import RealRooted.EffectiveBKW.PathCube.BranchBounds']
    imports += [f'import RealRooted.EffectiveBKW.PathCube.Boxes{i:02}'
                for i in range(len(blocks))]
    imports += [f'import RealRooted.EffectiveBKW.PathCube.Compatibility{i:02}'
                for i in range((count + 59) // 60)]
    return {'BranchFacts.lean': lean_module(imports, 'The continuous path-cube branch', body)}


def render_finite(cert):
    out = {}
    rows = [[1]] + cert['prefix']['generated_rows']
    grids = [[[0, 1]]] + [g['points'] for g in cert['prefix']['prefix_sign_grids']]
    body = ''
    for i, (row, points) in enumerate(zip(rows, grids)):
        body += declaration(f'rowCoeffs{i:02}', 'IntPoly', lean_list(row),
                            f'Ascending coefficients of row {i}.')
        body += declaration(f'points{i:02}', 'List QNum', lean_list(points, lean_q),
                            f'Exact sample points for row {i}.')
    body += declaration('rowLists', 'List IntPoly',
                       lean_list([f'rowCoeffs{i:02}' for i in range(len(rows))]),
                       'The first 59 rows, including the constant row at index zero.')
    body += declaration('gridPoints', 'List (List QNum)',
                        lean_list([f'points{i:02}' for i in range(len(rows))]),
                        'Exact increasing sign grids, ending at zero.')
    body += ('/-- Total lookup of an ascending coefficient list. -/\n'
             'def rowList (r : ℕ) : IntPoly := rowLists.getD r []\n\n'
             '/-- The rational sign grid for a row. -/\n'
             'def grid (r : ℕ) : SignGrid := ⟨rowList r, gridPoints.getD r []⟩\n\n'
             '/-- Integer-list version of the order-four transfer recurrence. -/\n'
             'def listStep (a b c d : IntPoly) : IntPoly :=\n'
             '  BigDescents321.SmallCases.addList\n'
             '    (BigDescents321.SmallCases.addList\n'
             '      (BigDescents321.SmallCases.addList\n'
             '        (BigDescents321.SmallCases.mulList [1, 3] a)\n'
             '        (BigDescents321.SmallCases.mulList [0, 2, -2] b))\n'
             '      (BigDescents321.SmallCases.mulList [0, 2, -1, -1] c))\n'
             '    (BigDescents321.SmallCases.mulList [0, 0, 1, -2, 1] d)\n')
    out['FiniteData.lean'] = lean_module(
        ['public import RealRooted.EffectiveBKW.Certificate.SignGrid'],
        'Exact finite path-cube data', body, True)
    for start in range(0, len(rows), 10):
        body = ''
        for r in range(start, min(start + 10, len(rows))):
            body += proof(f'grid{r:02}_check', f'(grid {r}).check = true',
                          f'The sign grid for row {r} passes the kernel checker.')
        out[f'FiniteChecks{start // 10:02}.lean'] = lean_module(
            ['public import RealRooted.EffectiveBKW.PathCube.FiniteData'],
            f'Finite path-cube sign grids {start} through {min(start + 9, len(rows) - 1)}', body)
    body = proof('rowLists_recurrence',
                 '∀ r : Fin 55, (rowList (r + 4)).eqCheck\n'
                 '      (listStep (rowList (r + 3)) (rowList (r + 2))\n'
                 '        (rowList (r + 1)) (rowList r)) = true',
                 'The 55 scalar recurrence steps are checked exactly on integer lists.')
    body += proof('grid_degrees', '∀ r : Fin 59, (grid r).degree = r.val',
                  'Each finite grid has exactly one more point than the row index.')
    body += proof('grid_last_points',
                  '∀ r : Fin 59, (grid r).point (grid r).degree = ⟨0, 1⟩',
                  'Every finite grid ends at the rational number zero.')
    out['FiniteRecurrence.lean'] = lean_module(
        ['public import RealRooted.EffectiveBKW.PathCube.FiniteData'],
        'Finite path-cube recurrence checks', body)
    return out


def render_endpoints(cert):
    out, body, checks = {}, '', ''
    endpoints = cert['endpoint_roots']
    body += declaration('endpointPolynomial', 'IntPoly', lean_list(endpoints['polynomial']),
                        'The quartic collision polynomial.')
    for aux, entry in cert['endpoint_auxiliary'].items():
        body += declaration('aux' + aux, 'IntPoly2', lean_poly2(entry['polynomial']),
                            'Reduced endpoint polynomial ' + aux + '.')
    for name, poly in [('aNumerator', A), ('aDenominator', d)]:
        body += declaration(name, 'IntPoly2', lean_poly2(dense(poly)),
                            'The ' + name + ' in the rational parametrization of the pair.')
    for side, entry in zip(['Left', 'Right'], endpoints['roots']):
        lo, hi = entry['interval']
        neg = str(entry['derivative_sign'] < 0).lower()
        body += declaration('endpoint' + side, 'IsolatedRoot',
                            f'⟨endpointPolynomial, {lean_q(lo)}, {lean_q(hi)}, {neg}⟩',
                            'An isolating interval for the ' + side.lower() + ' collision.')
        checks += proof('endpoint' + side + '_check',
                        'endpoint' + side + '.check = true',
                        'The quartic root is isolated by exact signs and a derivative check.')
        bx = entry['box']
        body += declaration('endpointCell' + side, 'BranchCell',
                            '⟨\n    ' + ',\n    '.join(map(lean_q, bx)) + '\n  ⟩',
                            'A simple resolvent root strip at the ' + side.lower() + ' collision.')
        cname = 'endpointCell' + side
        checks += proof(cname + '_check', f'{cname}.check curve false = true',
                        'The endpoint resolvent branch remains simple.')
        sign = str(entry['a_sign'] < 0).lower()
        for poly in ['aNumerator', 'auxREALF']:
            checks += proof(cname + '_' + poly,
                            f'({poly}.signed {sign}).posOnBox {cname}.tlo {cname}.thi\n'
                            f'      {cname}.lo {cname}.hi = true',
                            'The endpoint sign agrees with the prescribed orientation.')
        for i, item in enumerate(entry['cpos_sides']):
            cname = f'sideCell{side}{i}'
            body += declaration(cname, 'BranchCell',
                                '⟨\n    ' + ',\n    '.join(map(lean_q, item['box'])) + '\n  ⟩',
                                'A tight one-parameter strip on a side of the collision.')
            checks += proof(cname + '_check', f'{cname}.check curve false = true',
                            'The side strip contains a unique resolvent root.')
            neg = str(item['sign'] < 0).lower()
            checks += proof(cname + '_sign',
                            f'(auxCPOS.signed {neg}).posOnBox {cname}.tlo {cname}.thi\n'
                            f'      {cname}.lo {cname}.hi = true',
                            'The squared imaginary-part numerator has the prescribed side sign.')
            if (side, i) in [('Left', 0), ('Right', 1)]:
                parent = 'cell000' if side == 'Left' else f"cell{len(cert['branch']['cells'])-1:03}"
                checks += proof(cname + '_parent',
                                f'{cname}.compatible {parent} curve false = true',
                                'The outside side strip agrees with the global branch.')
                asign = str(entry['a_sign'] < 0).lower()
                checks += proof(cname + '_aNumerator',
                                f'(aNumerator.signed {asign}).posOnBox {cname}.tlo '
                                f'{cname}.thi\n      {cname}.lo {cname}.hi = true',
                                'The outside side strip has the required real-part sign.')
    for i, (lo, hi) in enumerate(endpoints['negative_gap_boxes']):
        checks += proof(f'endpointGap{i}_check',
                        f'(endpointPolynomial.signed true).posOn\n'
                        f'      {lean_q(lo)} {lean_q(hi)} = true',
                        'The collision polynomial is strictly negative on this gap interval.')
    out['EndpointData.lean'] = lean_module(
        ['public import RealRooted.EffectiveBKW.Certificate.Branch'],
        'Path-cube endpoint data', body, True)
    out['EndpointChecks.lean'] = lean_module(
        ['public import RealRooted.EffectiveBKW.PathCube.EndpointData',
         'public import RealRooted.EffectiveBKW.PathCube.CertificateData'],
        'Path-cube endpoint and side-sign checks', checks)
    return out


def render_algebra_data(cert):
    """Kernel witnesses connecting reduced signs with scalar rational parameters."""
    from fractions import Fraction
    definitions = [
        ('one', '[[1]]', '1'),
        ('t', '[[0, 1]]', 't'),
        ('b', '[[], [1]]', 'b'),
        ('s', '[[1, 3]]', '1 + 3 * t'),
        ('e', '[[0, -2, 2]]', '-2 * t * (1 - t)'),
        ('c', '[[0, 2, -1, -1]]', 't * (2 - t - t ^ 2)'),
        ('pi', '[[0, 0, -1, 2, -1]]', '-t ^ 2 * (1 - t) ^ 2'),
        ('d', 'aDenominator', '2 * (b ^ 2 - scalarPi t b)'),
        ('a', 'aNumerator', 'b * (b * scalarS t b - scalarC t b)'),
    ]
    def pn(name):
        return 'poly' + name[0].upper() + name[1:]
    def sn(name):
        return 'scalar' + name[0].upper() + name[1:]
    def plus(*xs):
        if len(xs) == 1:
            return xs[0]
        return f'({plus(*xs[:-1])}.add {xs[-1]})'
    def times(*xs):
        if len(xs) == 1:
            return xs[0]
        return f'({times(*xs[:-1])}.mul {xs[-1]})'
    def neg(x):
        return f'({x}.smul (-1))'
    def minus(x, y):
        return plus(x, neg(y))
    def powr(x, n):
        return f'({x}.pow {n})'
    def scale(x, n):
        return f'({x}.smul ({n}))'
    O, T, B, S, E, C, PI, D, A = [pn(v[0]) for v in definitions]
    J = minus(scale(A, 2), times(S, D))
    H = minus(scale(A, 4), times(S, D))
    K = minus(PI, powr(B, 2))
    U = minus(minus(minus(scale(powr(A, 2), 4), times(B, powr(D, 2))),
                      scale(times(T, A, D), 4)), scale(times(T, powr(D, 2)), 2))
    V = plus(scale(times(A, B), -2),
             times(minus(scale(times(T, B), 2), times(powr(T, 2), minus(O, T))), D))
    definitions += [
        ('j', J, '2 * scalarA t b - scalarS t b * scalarD t b'),
        ('h', H, '4 * scalarA t b - scalarS t b * scalarD t b'),
        ('k', K, 'scalarPi t b - b ^ 2'),
        ('u', U, '4 * scalarA t b ^ 2 - b * scalarD t b ^ 2 -\n'
         '    4 * t * scalarA t b * scalarD t b - 2 * t * scalarD t b ^ 2'),
        ('v', V, '-2 * scalarA t b * b +\n'
         '    (2 * t * b - t ^ 2 * (1 - t)) * scalarD t b'),
        ('l', plus(scale(times(A, pn('h'), B), 2), times(pn('k'), powr(D, 2))),
         '2 * scalarA t b * scalarH t b * b + scalarK t b * scalarD t b ^ 2'),
        ('nn', plus(times(powr(pn('u'), 2), B), scale(times(pn('u'), pn('v'), A), 2),
                    times(powr(pn('v'), 2), powr(D, 2))),
         'scalarU t b ^ 2 * b + 2 * scalarU t b * scalarV t b * scalarA t b +\n'
         '    scalarV t b ^ 2 * scalarD t b ^ 2'),
        ('hh', plus(times(powr(pn('h'), 2), powr(B, 3)),
                    scale(times(pn('h'), pn('k'), A, B), 2),
                    times(powr(pn('k'), 2), powr(D, 2))),
         'scalarH t b ^ 2 * b ^ 3 + 2 * scalarH t b * scalarK t b * scalarA t b * b +\n'
         '    scalarK t b ^ 2 * scalarD t b ^ 2'),
    ]
    exprs = {
        'G1': (plus(scale(powr(B, 2), 289), scale(PI, 400)), 400),
        'G2': (minus(times(powr('exprG1', 2), powr(D, 2)),
                     scale(times(powr(B, 3), powr(pn('j'), 2)), 115600)), 160000),
        'AMP': (minus(scale(times(B, pn('nn')), 100), times(powr(D, 2), pn('hh'))), 100),
        'W1': (minus(scale(B, 64), scale(powr(T, 2), 100)), 25),
        'W2': (minus(scale(powr(B, 2), 9), scale(powr(T, 2), 100)), 25),
        'W3': (minus(powr(B, 3), scale(times(powr(T, 4), powr(minus(O, T), 2)), 4)), 4),
        'WIND': (plus(times(pn('u'), pn('h'), powr(B, 2)), times(pn('v'), pn('l'))), 1),
        'CPOS': (minus(times(B, powr(D, 2)), powr(A, 2)), 1),
        'FACT': (plus(times(powr(B, 2), powr(D, 2)), times(PI, powr(D, 2)),
                      scale(times(A, pn('j'), B), -2), neg(times(E, B, powr(D, 2)))), 1),
    }
    body = ''
    known = []
    for name, expr, scalar in definitions:
        nameP, nameS = pn(name), sn(name)
        for short in ['s', 'e', 'c', 'pi']:
            scalar = scalar.replace(sn(short) + ' t b', sn(short) + ' t')
        body += f'/-- Integer-list expression for the scalar {name}. -/\ndef {nameP} : IntPoly2 :=\n'
        import textwrap
        body += '\n'.join(textwrap.wrap(expr, 94, initial_indent='  ', subsequent_indent='  ',
                                        break_long_words=False, break_on_hyphens=False)) + '\n\n'
        short = name in {'s', 'e', 'c', 'pi'}
        call = nameS + (' t' if short else ' t b')
        if name in {'one', 't', 'b'}:
            call = scalar
        else:
            body += (f'/-- Real scalar {name} in the rational factorization. -/\n'
                     f'noncomputable def {nameS} ({"t" if short else "t b"} : ℝ) : ℝ := '
                     f'{scalar}\n\n')
        if name in {'one', 't', 'b', 's', 'e', 'c', 'pi', 'd', 'a'}:
            args = [nameP]
            if name not in {'one', 't', 'b'}:
                args += [nameS]
            if name == 'd':
                args += ['aDenominator', 'scalarPi']
            if name == 'a':
                args += ['aNumerator', 'scalarS', 'scalarC']
            args += ['IntPoly2.eval', 'IntPoly.eval', 'IntPoly.polynomial',
                     'BigDescents321.SmallCases.ofList_cons',
                     'BigDescents321.SmallCases.ofList_nil',
                     'Polynomial.eval_add', 'Polynomial.eval_C', 'Polynomial.eval_mul',
                     'Polynomial.eval_X', 'Polynomial.eval_zero']
            proof = '  simp only [' + ', '.join(args) + ']\n  ring\n'
        else:
            args = [nameP, nameS]
            for op in ['add', 'mul', 'smul', 'pow']:
                if '.' + op in expr:
                    args.append('IntPoly2.eval_' + op)
            args += ['eval_' + p for p in known if p in expr]
            import re
            if '(-' in expr:
                args.append('Int.cast_neg')
            if '(-1)' in expr:
                args.append('Int.cast_one')
            if re.search(r'\.smul \(-?[2-9][0-9]*\)', expr):
                args.append('Int.cast_ofNat')
            tactic = 'simp only'
            if name in {'l', 'nn', 'hh'}:
                args.append('mul_assoc')
            proof = '  ' + tactic + ' [' + ', '.join(args) + ']\n'
            if name not in {'l', 'nn', 'hh'}:
                proof += '  ring\n'
        body += (f'/-- Scalar interpretation of the list expression {name}. -/\n'
                 f'theorem eval_{nameP} (t b : ℝ) : {nameP}.eval t b = {call} := by\n' +
                 proof + '\n')
        known.append(nameP)
    for name, (expr, den) in exprs.items():
        body += f'/-- Denominator-cleared expression for {name}. -/\ndef expr{name} : IntPoly2 :=\n'
        body += '\n'.join(textwrap.wrap(expr, 94, initial_indent='  ', subsequent_indent='  ',
                                        break_long_words=False, break_on_hyphens=False)) + '\n\n'
        if name == 'FACT':
            raw = cert['factorization_witness']['identities'][1]
            quotient = raw['quotient']
            reduced_name, content, factor = None, 0, one
            mult = 1
        else:
            obj = (cert['endpoint_auxiliary'] if name == 'CPOS' else cert['sign_conditions'])[name]
            r = obj['reduction']
            mult = Fraction(den, r['rational_denominator'])
            assert mult.denominator == 1
            mult = int(mult)
            quotient = dense({(i, j): v * mult for j, row in enumerate(r['quotient'])
                              for i, v in enumerate(row) if v})
            reduced_name = 'auxCPOS' if name == 'CPOS' else 'condition' + name
            content = r['content'] * mult
            factor = mul(power({(1, 0): -1}, r['positive_factor']['negative_t_power']),
                         power(sub(one, t), r['positive_factor']['one_minus_t_power']))
        body += (f'/-- Exact quotient witness for {name}. -/\ndef quotient{name} : IntPoly2 :=\n'
                 + lean_poly2(quotient) + '\n\n')
        rhs = f'(quotient{name}.mul curve)'
        if reduced_name:
            body += (f'/-- Positive factor removed from condition {name}. -/\n'
                     f'def factor{name} : IntPoly2 :=\n' + lean_poly2(dense(factor)) + '\n\n')
            rhs = f'({rhs}.add (({reduced_name}.smul {content}).mul factor{name}))'
        body += (f'/-- The exact list identity for {name} is checked by the kernel. -/\n'
                 f'theorem expr{name}_check : expr{name}.eqCheck\n    {rhs} = true := by\n'
                 '  decide +kernel\n\n')
        if reduced_name:
            k = r['positive_factor']['negative_t_power']
            h = r['positive_factor']['one_minus_t_power']
            factor_value = f'(-t) ^ {k} * (1 - t) ^ {h}'
            body += (f'/-- Interpretation of the removed positive factor for {name}. -/\n'
                     f'theorem eval_factor{name} (t b : ℝ) :\n'
                     f'    factor{name}.eval t b = {factor_value} := by\n'
                     f'  simp only [factor{name}, IntPoly2.eval, IntPoly.eval, IntPoly.polynomial,\n'
                     '    BigDescents321.SmallCases.ofList_cons,\n'
                     '    BigDescents321.SmallCases.ofList_nil, Polynomial.eval_add,\n'
                     '    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,\n'
                     '    Polynomial.eval_zero]\n  ring\n\n')
            body += (f'/-- The reduction identity holds on the resolvent curve. -/\n'
                     f'theorem eval_expr{name} {{t b : ℝ}} (hc : curve.eval t b = 0) :\n'
                     f'    expr{name}.eval t b = {content} * {reduced_name}.eval t b *\n'
                     f'      ({factor_value}) := by\n'
                     f'  have he := IntPoly2.eqCheck_sound expr{name}_check t b\n'
                     '  simpa only [IntPoly2.eval_add, IntPoly2.eval_mul, IntPoly2.eval_smul,\n'
                     f'    hc, mul_zero, zero_add, eval_factor{name}, '
                     + ('Int.cast_one' if content == 1 else 'Int.cast_ofNat') + '] using he\n\n')
            if name != 'CPOS':
                ht = '(ht : t < 0) ' if k or h else ''
                body += (f'/-- A reduced positive sign yields the denominator-cleared sign. -/\n'
                         f'theorem expr{name}_pos {{t b : ℝ}} {ht}(hc : curve.eval t b = 0)\n'
                         f'    (hp : 0 < {reduced_name}.eval t b) : 0 < expr{name}.eval t b := by\n'
                         f'  rw [eval_expr{name} hc]\n')
                if k or h:
                    body += ('  have hn : 0 < -t := neg_pos.mpr ht\n'
                             '  have ho : 0 < 1 - t := by linarith\n')
                body += '  positivity\n\n'
    body = '\n'.join('\n'.join(textwrap.wrap(line, width=98,
                     subsequent_indent=' ' * (len(line) - len(line.lstrip()) + 2),
                     break_long_words=False, break_on_hyphens=False))
                     if len(line) > 98 else line for line in body.splitlines()) + '\n'
    return {'AlgebraData.lean': lean_module(
        ['public import RealRooted.EffectiveBKW.PathCube.CertificateData',
         'public import RealRooted.EffectiveBKW.PathCube.EndpointData',
         'import Mathlib.Tactic.Ring', 'import Mathlib.Tactic.Linarith',
         'import Mathlib.Tactic.Positivity'],
        'Scalar expressions and exact reduction witnesses', body, exposed=True)}


def generated_files(cert):
    prefix = Path('RealRooted/EffectiveBKW/PathCube')
    result = {prefix / name: value for name, value in
              (render_certificate(cert) | render_finite(cert) | render_endpoints(cert) |
               render_branch_facts(cert) | render_algebra_data(cert)).items()}
    result[Path('scripts/ebkw_pathcube_certificate.json')] = (
        json.dumps(cert, separators=(',', ':')) + '\n')
    return result


def make_certificate():
    endpoints = [isolate_q(-40, -39), isolate_q(F(-1, 20), F(-1, 100))]
    return produce('wide', F(17, 20), F(1, 10),
                   [F(1), F(8, 5), F(3, 5), F(1, 2)], endpoints, bezout())


def self_test(cert):
    import copy
    replay_verify(cert)
    damaged = copy.deepcopy(cert)
    damaged['branch']['cells'][0][2] = damaged['branch']['cells'][0][3]
    try:
        replay_verify(damaged)
    except AssertionError:
        pass
    else:
        raise RuntimeError('corrupted zero-width branch cell was accepted')
    damaged = copy.deepcopy(cert)
    damaged['sign_conditions']['G2']['polynomial'][0][0] += 1
    try:
        replay_verify(damaged)
    except AssertionError:
        pass
    else:
        raise RuntimeError('corrupted condition polynomial was accepted')
    damaged = copy.deepcopy(cert)
    damaged['prefix']['prefix_sign_grids'][-1]['points'][1] = [0, 1]
    try:
        replay_verify(damaged)
    except AssertionError:
        pass
    else:
        raise RuntimeError('corrupted finite grid was accepted')
    return {'replay': 'passed', 'corrupt_cell': 'rejected',
            'corrupt_condition': 'rejected', 'corrupt_grid': 'rejected'}


def combine_module(root, module, timed=False):
    """Combine new modules for the authorized single-file elaboration wrapper.

    Existing modules remain imports and use the coordinator's built environment.
    This does not produce oleans or replace authoritative module builds.
    """
    seen, imports, bodies = set(), [], []

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        source = root / (name.replace('.', '/') + '.lean')
        body = []
        source_text = source.read_text()
        for line in source_text.splitlines():
            if line.startswith(('import ', 'public import ')):
                target = line.split()[-1]
                if target.startswith('RealRooted.EffectiveBKW.PathCube.'):
                    visit(target)
                else:
                    imports.append(line)
            elif line != 'module':
                body.append(line)
        if timed:
            import re
            theorem_names, namespaces = [], []
            for line in source_text.splitlines():
                if line.startswith('namespace '):
                    namespaces.append(line.split()[1])
                elif line.startswith('end ') and namespaces:
                    namespaces.pop()
                else:
                    declaration_match = re.match(r'^(?:@\[simp\] )?theorem (\w+)', line)
                    if declaration_match:
                        theorem_names.append('.'.join(namespaces + [declaration_match[1]]))
            start = (f'#eval show IO Unit from do\n'
                     f'  IO.println s!"EBKW_BEGIN {name} {{← IO.monoMsNow}}"\n')
            audits = '\n'.join('#print axioms ' + thm for thm in theorem_names)
            stop = (f'\n#eval show IO Unit from do\n'
                    f'  IO.println s!"EBKW_END {name} {{← IO.monoMsNow}}"\n')
            bodies.append(start + '\n'.join(body) + '\n' + audits + stop)
        else:
            bodies.append('\n'.join(body))

    for selected in module.split(','):
        visit(selected)
    return 'module\n\n' + '\n'.join(dict.fromkeys(imports)) + '\n\n' + '\n'.join(bodies) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['generate', 'check', 'test', 'combine'])
    parser.add_argument('--root', type=Path, default=HERE)
    parser.add_argument('--module', help='Comma-separated fully qualified PathCube modules for combine')
    parser.add_argument('--output', type=Path, help='Combined scratch file (combine only)')
    parser.add_argument('--timed', action='store_true',
                        help='Emit per-module timing markers and theorem axiom audits')
    args = parser.parse_args()
    if args.action == 'combine':
        if not args.module or not args.output:
            parser.error('combine requires --module and --output')
        args.output.write_text(combine_module(args.root, args.module, args.timed))
        return
    started = time.monotonic()
    cert = make_certificate()
    result = self_test(cert)
    if args.action != 'test':
        generated = generated_files(cert)
        for relative, content in generated.items():
            destination = args.root / relative
            if args.action == 'generate':
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text(content)
            elif not destination.exists() or destination.read_text() != content:
                raise RuntimeError('not reproducible: ' + str(relative))
        result['files'] = len(generated)
    result.update(cells=len(cert['branch']['cells']), N0=cert['N0'],
                  seconds=round(time.monotonic() - started, 3))
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()


