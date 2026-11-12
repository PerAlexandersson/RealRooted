module

public import RealRooted.Bezoutian
public import RealRooted.Bezoutian.ComplexRoots
public import RealRooted.Bezoutian.LowDegree
public import RealRooted.Bezoutian.MatrixBasics
public import RealRooted.Bezoutian.RootEvaluation
public import RealRooted.Bezoutian.StrictInterleaving
public import RealRooted.Bezoutian.Successor
public import RealRooted.Mathlib.Algebra.Polynomial.Bezoutian

/-!
# Bézout matrices and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "bezoutian"
formalized = "2026-10-06"
tags = []
references = [
  "Fisk2006x",
]
authors = ["Hermite", "Krein", "Naimark", "Fisk"]
years = [1856, 1936, 2006]

[[definitions]]
name = "Polynomial.bezoutMatrix"
module = "RealRooted.Mathlib.Algebra.Polynomial.Bezoutian"
label = "Bézout matrix"

[[definitions]]
name = "RealRooted.StrictInterlSameDegree"
module = "RealRooted.Bezoutian.StrictInterleaving"
label = "Strict interlacing of equal-degree polynomials"

[[theorems]]
name = "RealRooted.strictInterlSameDegree_iff_bezoutMatrix_posDef"
module = "RealRooted.Bezoutian.LowDegree"
label = "Strict interlacing is positive definiteness of the Bézout matrix"
headline = true

[[theorems]]
name = "RealRooted.bezoutMatrix_posDef_iff_interlaces_succ"
module = "RealRooted.Bezoutian.Successor"
label = "Successor-degree interlacing is positive definiteness of the Bézout matrix"

[[theorems]]
name = "RealRooted.bezoutMatrix.splits_of_posDef"
module = "RealRooted.Bezoutian.ComplexRoots"
label = "A positive definite Bézout matrix forces real roots"

[[theorems]]
name = "RealRooted.bezoutMatrix.wronskian_pos_of_posDef"
module = "RealRooted.Bezoutian.RootEvaluation"
label = "A positive definite Bézout matrix gives a positive Wronskian"
-->

<!-- realrooted-catalog-content -->
# Bézout matrices and interlacing

Two real polynomials of equal degree have strictly interlacing real roots if and only if their
Bézout matrix is positive definite.

## Results

For real polynomials $p$ and $q$ of degree at most $n$, the Bézoutian
$$
\frac{q(x)\,p(y) - q(y)\,p(x)}{x - y} = \sum_{i,j=0}^{n-1} b_{ij}\, x^i y^j
$$
is a polynomial. Its coefficient matrix $B_n(q,p) = (b_{ij})$ is the symmetric $n \times n$
*Bézout matrix*.

**Theorem (equal degree).** Let $p$ and $q$ have degree $n$ and positive leading coefficients.
Then $p$ and $q$ are real-rooted with strictly interlacing roots,
$$
\alpha_1 < \beta_1 < \alpha_2 < \beta_2 < \dots < \alpha_n < \beta_n,
$$
where $\alpha_i$ and $\beta_i$ are the roots of $p$ and $q$, if and only if $B_n(q,p)$ is
positive definite. If $B_n(q,p)$ is positive definite, then $p$ and $q$ are real-rooted.

**Theorem (successor degree).** [@Fisk2006x, Cor. 9.145] Let $f$ have degree $d+1$ and $g$
degree $d$, both with positive leading coefficients. Then $B_{d+1}(f,g)$ is positive definite
if and only if $g$ interlaces $f$ and the two polynomials have no common root, that is,
$$
\alpha_1 < \beta_1 < \alpha_2 < \dots < \beta_d < \alpha_{d+1}
$$
for the roots $\alpha_i$ of $f$ and $\beta_i$ of $g$.

**Proposition (Wronskian).** Let $p$ and $q$ have degree at most $n$. If $B_n(q,p)$ is positive
definite, then $q'(t)\,p(t) - q(t)\,p'(t) > 0$ for all real $t$.

## Proof

Evaluating the Bézoutian at the roots of one polynomial gives Wronskian values. Congruence
with a Vandermonde matrix therefore turns the Bézout matrix into a diagonal matrix whose
entries have the signs of the Wronskian at those roots, and these are positive exactly when the
roots interlace. Conversely, a positive definite Bézout matrix makes the Wronskian positive,
which excludes common real roots, and it excludes non-real roots because its Hermitian form
would vanish on a conjugate pair.

## References

C. Hermite, “Sur le nombre des racines d'une équation algébrique comprise
entre des limites données,” *J. Reine Angew. Math.* 52 (1856), 39–51;
M. G. Krein and M. A. Naimark, “The method of symmetric and Hermitian forms in
the theory of the separation of the roots of algebraic equations” (1936),
English translation in *Linear and Multilinear Algebra* 10 (1981), 265–308.
The successor-degree criterion is [@Fisk2006x, Cor. 9.145]. See the
[contextual statement on symmetricfunctions.com](sf:bezoutMatrix).
<!-- /realrooted-catalog-content -->

This module exposes the checked same-degree and successor-degree Bézout
criteria. The matrix algebra, root evaluation, complex-root, and low-degree
layers live in `RealRooted.Bezoutian`; the successor-degree proof lives in
`RealRooted.Bezoutian.Successor`.
-/
