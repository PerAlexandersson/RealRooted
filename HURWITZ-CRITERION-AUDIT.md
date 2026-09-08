# Classical Hurwitz-Matrix Criterion Audit

This note records the theorem shape and checked strict criterion for issue
#551. It distinguishes the classical matrix from the lower-triangular Lace
matrix historically called `RealRooted.hurwitz`.

## Primary sources

- Olga Holtz, *Hermite--Biehler, Routh--Hurwitz, and total positivity*,
  [arXiv:math/0512591](https://arxiv.org/abs/math/0512591), Theorems 3--4.
- Mohammad Adm, Jürgen Garloff, and Mikhail Tyaglov, *Total nonnegativity of
  finite Hurwitz matrices and root location of polynomials*,
  [arXiv:1711.04651](https://arxiv.org/abs/1711.04651), especially Theorems
  4.5, 4.9, and 4.10.

Holtz indexes coefficients from the constant term:

```text
f(X) = c 0 + c 1 * X + ... + c n * X^n.
```

The classical infinite matrix in that convention is

```text
c 0  c 2  c 4  c 6  ...
0    c 1  c 3  c 5  ...
0    c 0  c 2  c 4  ...
0    0    c 1  c 3  ...
...  ...  ...  ...
```

Thus its entry is

```text
H(c) i j = if i ≤ 2 * j then c (2 * j - i) else 0.
```

This is now `Matrix.hurwitz`. Its order-`n` finite leading section is
`Matrix.hurwitzLeadingPrincipal c n`.

Adm--Garloff--Tyaglov index `a 0` from the leading term downward. Their matrix
therefore uses the reversed finite coefficient list when translated to Lean's
constant-term-first `Polynomial.coeff`. Both conventions are legitimate, but
they must not be mixed in one theorem statement.

## Distinction from the Lace matrix

`RealRooted.hurwitz c` is lower triangular. Its even rows contain the Toeplitz
matrix of the odd coefficients, and its odd rows contain the Toeplitz matrix of
the even coefficients. It was designed so that the matrix of
`oddEvenPolynomial p q` is literally `lacePair p.coeff q.coeff`.

By contrast, `Matrix.hurwitz` is upper triangular by shifted row pairs. For
`oddEvenPolynomial p q = q(X²) + X * p(X²)`:

- even rows are the transpose of `toeplitz q.coeff`;
- odd rows are the transpose of `toeplitz p.coeff`, shifted one row; and
- no order-preserving row or column relabeling identifies it with `lacePair`.

Accordingly, total nonnegativity cannot be transferred between these matrices
by a cosmetic transpose or row swap.

## Exact regressions and finite indexing

The first leading determinants over a commutative ring are

```text
Δ₀ = 1
Δ₁ = c 0
Δ₂ = c 0 * c 1
Δ₃ = c 0 * (c 1 * c 2 - c 0 * c 3).
```

For the stored counterexample `X^3 + 1`, `Δ₃ = -1`. Hence its classical
Hurwitz matrix is not totally nonnegative, even though its Lace-oriented
matrix is totally nonnegative. This directly tests the corrected convention
against the repository's existing false-interface witness.

The order-`n` leading section depends only on coefficients with index less
than `2 * n`; `Matrix.hurwitzLeadingPrincipal_congr` makes this finite support
boundary explicit.

## Stability hypotheses and valid theorem shapes

Holtz uses strict stability: every root has strictly negative real part, with
positive constant coefficient. Her Theorem 4 proves that strict stability
implies total nonnegativity of the infinite classical matrix.

Adm--Garloff--Tyaglov distinguish:

- strict stability, characterized by positivity of all Hurwitz determinants,
  equivalently by a nonsingular totally nonnegative finite Hurwitz matrix; and
- quasi-stability, meaning that every root lies in the closed left half-plane.
  Under their nonzero leading- and constant-coefficient convention, Theorem
  4.10 characterizes quasi-stability by total nonnegativity of the infinite
  Hurwitz matrix.

The project's `IsHurwitzStable` is the coefficient-nonnegative, quasi-stable
predicate: it excludes roots only from the open right half-plane. It is not
Holtz's strict predicate. Therefore:

- a strict theorem must introduce an explicit strict root-location predicate;
- a theorem using `IsHurwitzStable` must be a closed-half-plane theorem;
- the zero polynomial remains excluded explicitly;
- boundary cases with a zero constant coefficient require a separate reduction
  or limit argument; and
- total nonnegativity of an arbitrary finite truncation is not a converse.
  The finite converse needs nonsingularity or the sharper minor conditions in
  the cited finite-matrix results.

## Formalization route

The strict route is now checked:

1. `Matrix.hurwitz` and `Matrix.hurwitzLeadingPrincipal` fix the corrected
   convention independently of stability theory.
2. `RealRooted.IsStrictlyHurwitzStable` records strict left-half-plane root
   location, while `oddEvenPolynomial_contract_divX_contract` gives the
   canonical parity representation of every real polynomial.
3. The Routh modules prove the matrix factorization, determinant recurrence,
   one-step forward and reverse stability theorems, and their finite
   iteration.
4. `Matrix.hurwitz_isTotallyNonneg_of_strictlyStable` proves the
   polynomial-level total-nonnegativity direction.
5. `Matrix.strictlyHurwitzStable_of_hurwitzLeadingPrincipal_det_pos` proves
   the determinant-positive converse by exact degree descent.
6. `Matrix.strictlyHurwitzStable_iff_hurwitzLeadingPrincipal_det_pos` is the
   strict Routh--Hurwitz equivalence under positive leading coefficient.
7. `Matrix.strictlyHurwitzStable_iff_hurwitz_isTotallyNonneg_and_det_pos`
   packages the exact strict matrix endpoint: total nonnegativity is paired
   with strict leading-determinant positivity.

The quasi-stable equivalence for boundary cases remains a separate future
closure problem. Total nonnegativity alone is intentionally not reported as a
strict converse.

The existing false Lace-oriented statements and their checked negations remain
unchanged throughout this route.
