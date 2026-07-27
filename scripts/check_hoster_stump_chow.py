#!/usr/bin/env python3
"""Finite checks for the Hoster--Stump refined Chow polynomial route.

The checker uses exact integer coefficient arithmetic for the refined
polynomials p_{n,k}^{S subset T}.  It compares the permutation definition with
the Section 3 recurrence, checks the deletion/relaxation identity, and verifies
the Theorem 3.3 diagram for T = [1,n] and T = [1,n-1] in a finite range.

The interlacing check uses SymPy's exact real algebraic roots for the small
polynomials in the default range.  If SymPy cannot decide one of the required
root inequalities exactly, the script fails instead of using a numerical
acceptance test.
"""

from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
from typing import Iterable, Iterator

import sympy as sp


x = sp.Symbol("x")
Poly = tuple[int, ...]
IndexSet = frozenset[int]


class CheckFailure(AssertionError):
    """Raised when a finite Hoster--Stump check fails."""


def normalize(coeffs: Iterable[int]) -> Poly:
    values = list(coeffs)
    while values and values[-1] == 0:
        values.pop()
    return tuple(values)


def monomial(degree: int, coeff: int = 1) -> Poly:
    if coeff == 0:
        return ()
    return normalize([0] * degree + [coeff])


def poly_add(*polys: Poly) -> Poly:
    max_len = max((len(poly) for poly in polys), default=0)
    coeffs = [0] * max_len
    for poly in polys:
        for i, coeff in enumerate(poly):
            coeffs[i] += coeff
    return normalize(coeffs)


def poly_mul_x(poly: Poly) -> Poly:
    return () if not poly else (0,) + poly


def poly_expr(poly: Poly) -> sp.Expr:
    return sum(coeff * x**degree for degree, coeff in enumerate(poly))


def all_subsets(values: Iterable[int]) -> Iterator[IndexSet]:
    items = list(values)
    for size in range(len(items) + 1):
        for subset in combinations(items, size):
            yield frozenset(subset)


def is_isolated(values: IndexSet) -> bool:
    return all(i + 1 not in values for i in values)


def descents(word: tuple[int, ...]) -> IndexSet:
    return frozenset(i + 1 for i in range(len(word) - 1) if word[i] > word[i + 1])


def shift_down(values: IndexSet) -> IndexSet:
    """Shift positive descent positions down and drop the vanished first one."""

    return frozenset(i - 1 for i in values if i > 1)


@lru_cache(maxsize=None)
def refined_poly_bruteforce(n: int, k: int, lower: IndexSet, upper: IndexSet) -> Poly:
    counts: Counter[int] = Counter()
    for word in permutations(range(1, n + 2)):
        if word[0] != k + 1:
            continue
        descent_set = descents(word)
        if is_isolated(descent_set) and lower <= descent_set <= upper:
            counts[len(descent_set)] += 1
    return normalize(counts.get(i, 0) for i in range(max(counts, default=-1) + 1))


@lru_cache(maxsize=None)
def refined_poly_recursive(n: int, k: int, lower: IndexSet, upper: IndexSet) -> Poly:
    if n == 1:
        if k == 0 and not lower:
            return (1,)
        if k == 1 and upper == frozenset({1}):
            return monomial(1)
        return ()

    lower_shift = shift_down(lower)
    upper_shift = shift_down(upper)
    summands: list[Poly] = []

    if 1 in upper:
        shifted_upper_without_first = upper_shift - {1}
        summands.append(
            poly_mul_x(
                poly_add(
                    *(
                        refined_poly_recursive(
                            n - 1, j, lower_shift, shifted_upper_without_first
                        )
                        for j in range(k)
                    )
                )
            )
        )

    if 1 not in lower:
        summands.append(
            poly_add(
                *(
                    refined_poly_recursive(n - 1, j, lower_shift, upper_shift)
                    for j in range(k, n)
                )
            )
        )

    return poly_add(*summands)


@lru_cache(maxsize=None)
def real_roots(poly: Poly) -> tuple[sp.Expr, ...]:
    if not poly:
        raise CheckFailure("the zero polynomial has no strict interlacing roots")

    expr = poly_expr(poly)
    sympy_poly = sp.Poly(expr, x, domain=sp.QQ)
    roots = tuple(sympy_poly.real_roots())
    if len(roots) != sympy_poly.degree():
        raise CheckFailure(f"not real-rooted: {sp.factor(expr)} has roots {roots}")
    return roots


def exact_le(left: sp.Expr, right: sp.Expr) -> bool:
    decision = (right - left).is_nonnegative
    if decision is None:
        raise CheckFailure(f"SymPy could not decide exact inequality {left} <= {right}")
    return bool(decision)


def prec(left: Poly, right: Poly) -> bool:
    if not left or not right:
        return False

    left_roots = real_roots(left)
    right_roots = real_roots(right)

    if len(right_roots) == len(left_roots) + 1:
        return all(
            exact_le(right_roots[i], left_roots[i])
            and exact_le(left_roots[i], right_roots[i + 1])
            for i in range(len(left_roots))
        )

    if len(right_roots) == len(left_roots):
        return all(
            exact_le(left_roots[i], right_roots[i])
            for i in range(len(left_roots))
        ) and all(
            exact_le(right_roots[i], left_roots[i + 1])
            for i in range(len(left_roots) - 1)
        )

    return False


def prec0(left: Poly, right: Poly) -> bool:
    return not left or not right or prec(left, right)


def interlacing_sequence(polys: list[Poly]) -> bool:
    nonzero = [poly for poly in polys if poly]
    return all(
        prec(nonzero[i], nonzero[j])
        for i in range(len(nonzero))
        for j in range(i + 1, len(nonzero))
    )


def valid_bounds(n: int) -> Iterator[tuple[IndexSet, IndexSet]]:
    universe = range(1, n + 1)
    for lower in all_subsets(universe):
        if not is_isolated(lower):
            continue
        for upper in all_subsets(universe):
            if lower <= upper:
                yield lower, upper


def verify_recurrence(max_n: int) -> int:
    checked = 0
    for n in range(1, max_n + 1):
        for lower, upper in valid_bounds(n):
            for k in range(n + 1):
                brute = refined_poly_bruteforce(n, k, lower, upper)
                rec = refined_poly_recursive(n, k, lower, upper)
                if brute != rec:
                    raise CheckFailure(
                        "recurrence mismatch for "
                        f"n={n}, k={k}, S={sorted(lower)}, T={sorted(upper)}: "
                        f"brute={sp.factor(poly_expr(brute))}, "
                        f"rec={sp.factor(poly_expr(rec))}"
                    )
                checked += 1
    return checked


def verify_deletion_relaxation(max_n: int) -> int:
    checked = 0
    for n in range(1, max_n + 1):
        for lower, upper in valid_bounds(n):
            for s in lower:
                for k in range(n + 1):
                    left = refined_poly_bruteforce(n, k, lower - {s}, upper)
                    right = poly_add(
                        refined_poly_bruteforce(n, k, lower, upper),
                        refined_poly_bruteforce(n, k, lower - {s}, upper - {s}),
                    )
                    if left != right:
                        raise CheckFailure(
                            "deletion/relaxation mismatch for "
                            f"n={n}, k={k}, s={s}, "
                            f"S={sorted(lower)}, T={sorted(upper)}"
                        )
                    checked += 1
    return checked


def diagram_rows(n: int, upper: IndexSet) -> tuple[list[Poly], list[Poly], list[Poly]]:
    top = [
        refined_poly_recursive(n, k, frozenset(), upper - {1})
        for k in range(n + 1)
    ]
    middle = [
        refined_poly_recursive(n, k, frozenset(), upper)
        for k in range(n + 1)
    ]
    bottom = [
        refined_poly_recursive(n, k, frozenset({1}), upper)
        for k in range(n + 1)
    ]
    return top, middle, bottom


def verify_theorem33_diagrams(max_n: int) -> int:
    checked = 0
    for n in range(2, max_n + 1):
        for upper in (frozenset(range(1, n)), frozenset(range(1, n + 1))):
            top, middle, bottom = diagram_rows(n, upper)
            row_checks = {
                "top": interlacing_sequence(top),
                "middle": interlacing_sequence(middle),
                "bottom": interlacing_sequence(bottom),
            }
            column_checks = {
                f"column {k}": interlacing_sequence([top[k], middle[k], bottom[k]])
                for k in range(n + 1)
            }
            diagonal_check = prec0(top[n - 1], bottom[1])
            checks = row_checks | column_checks | {"diagonal": diagonal_check}
            failures = [name for name, ok in checks.items() if not ok]
            if failures:
                raise CheckFailure(
                    f"Theorem 3.3 diagram failed for n={n}, T={sorted(upper)}: "
                    f"{', '.join(failures)}"
                )
            checked += len(checks)
    return checked


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-n",
        type=int,
        default=5,
        help="largest n to brute-force; default is 5 for a fast CI-style check",
    )
    args = parser.parse_args()

    if args.max_n < 1:
        raise SystemExit("--max-n must be at least 1")

    recurrence_checks = verify_recurrence(args.max_n)
    deletion_checks = verify_deletion_relaxation(args.max_n)
    diagram_checks = verify_theorem33_diagrams(args.max_n)

    print(f"Hoster--Stump refined Chow checks passed through n={args.max_n}.")
    print(f"  recurrence vs brute force instances: {recurrence_checks}")
    print(f"  deletion/relaxation instances: {deletion_checks}")
    print(f"  Theorem 3.3 row/column/diagonal checks: {diagram_checks}")


if __name__ == "__main__":
    main()
