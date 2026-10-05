import RealRooted.Bezoutian

/-!
# Bézout matrices and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "bezoutian"
authors = ["Hermite", "Krein", "Naimark", "Fisk"]
years = [1856, 1936, 2006]

[[definitions]]
name = "RealRooted.bezoutMatrix"
module = "RealRooted.Bezoutian.MatrixBasics"
label = "Bézout matrix"

[[definitions]]
name = "RealRooted.StrictInterlSameDegree"
module = "RealRooted.Bezoutian.StrictInterleaving"
label = "Strict interlacing of equal-degree polynomials"

[[theorems]]
name = "RealRooted.Challenges.Bezoutian.strictInterlSameDegree_iff_posDef"
label = "Strict interlacing is positive definiteness of the Bézout matrix"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Bezoutian.splits_of_posDef"
label = "A positive definite Bézout matrix forces real roots"

[[theorems]]
name = "RealRooted.Challenges.Bezoutian.wronskian_pos_of_posDef"
label = "A positive definite Bézout matrix gives a positive Wronskian"
-->

<!-- realrooted-catalog-content -->
# Bézout matrices and interlacing

For real polynomials $p$ and $q$ of degree at most $n$, the Bézoutian
$$
\frac{q(x)\,p(y) - q(y)\,p(x)}{x - y} = \sum_{i,j=0}^{n-1} b_{ij}\, x^i y^j
$$
is a polynomial, and its coefficient matrix $B_n(q,p) = (b_{ij})$ is the
symmetric $n \times n$ **Bézout matrix**.

**Theorem.** Let $p$ and $q$ have degree $n$ and positive leading
coefficients. Then $p$ and $q$ are both real-rooted with strictly interlacing
zeros,
$$
\alpha_1 < \beta_1 < \alpha_2 < \beta_2 < \dots < \alpha_n < \beta_n,
$$
where $\alpha_i$ and $\beta_i$ are the zeros of $p$ and $q$, if and only if
$B_n(q,p)$ is positive definite.

Positive definiteness alone already forces both polynomials to split over
$\mathbb R$, and it makes the Wronskian $q'p - qp'$ positive on all of
$\mathbb R$.

The successor-degree form of Bézout's theorem, where $\deg f = \deg g + 1$ and
$g$ strictly interlaces $f$ if and only if $B(f,g)$ is positive definite, is
not yet formalized here.

## Proof idea

Evaluating the Bézoutian at a root of $p$ and at a root of $q$ gives Wronskian
values, so congruence with a Vandermonde matrix turns $B_n(q,p)$ into a
diagonal matrix whose entries have the signs of $q'p - qp'$ at the roots. Those
signs are positive exactly when the zeros interlace. Conversely, a positive
definite Bézoutian has no common real root with either polynomial and rules
out non-real roots, because the Hermitian form vanishes on the conjugate pair.

## References

C. Hermite, “Sur le nombre des racines d'une équation algébrique comprise
entre des limites données,” *J. Reine Angew. Math.* 52 (1856), 39–51;
M. G. Krein and M. A. Naimark, “The method of symmetric and Hermitian forms in
the theory of the separation of the roots of algebraic equations” (1936),
English translation in *Linear and Multilinear Algebra* 10 (1981), 265–308;
S. Fisk, *Polynomials, roots, and interlacing*, arXiv:math/0612833, Cor. 9.145.
See the
[contextual statement on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#bezoutMatrix).
<!-- /realrooted-catalog-content -->

This module exposes the checked same-degree Bézout criterion. The matrix
algebra, root evaluation, complex-root, and low-degree layers live in
`RealRooted.Bezoutian`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Bezoutian

/-- **Bézout's criterion** for equal degrees: two real polynomials of degree
`n` with positive leading coefficients strictly interlace if and only if their
Bézout matrix is positive definite. -/
theorem strictInterlSameDegree_iff_posDef {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    StrictInterlSameDegree p q ↔ (bezoutMatrix n q p).PosDef :=
  strictInterlSameDegree_iff_bezoutMatrix_posDef hp_pos hq_pos hp_deg hq_deg

/-- A positive definite Bézout matrix forces both polynomials to split over
`ℝ`. -/
theorem splits_of_posDef {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hB : (bezoutMatrix n q p).PosDef) :
    p.Splits ∧ q.Splits :=
  bezoutMatrix.splits_of_posDef hp_pos hq_pos hp_deg hq_deg hB

/-- A positive definite Bézout matrix makes the Wronskian `q' p - q p'`
positive everywhere. -/
theorem wronskian_pos_of_posDef {p q : ℝ[X]} {n : ℕ}
    (hq_deg : q.natDegree ≤ n + 1) (hp_deg : p.natDegree ≤ n + 1)
    (hB : (bezoutMatrix (n + 1) q p).PosDef) (t : ℝ) :
    0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t :=
  bezoutMatrix.wronskian_pos_of_posDef hq_deg hp_deg hB t

end Bezoutian
end Challenges
end RealRooted
