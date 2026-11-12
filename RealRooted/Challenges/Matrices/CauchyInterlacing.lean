module

import RealRooted.CauchyInterlacing.Polynomial
public import RealRooted.CauchyInterlacing.RankOne
public import RealRooted.CauchyInterlacing
public import RealRooted.Basic.ProperPosition

/-!
# Cauchy interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "cauchy-interlacing"
formalized = "2026-07-10"
tags = []
references = [
  "Godsil2017",
  "Fisk2005x",
]
authors = ["Fisk"]
years = [2005]

[[theorems]]
name = "RealRooted.Challenges.CauchyInterlacing.principalSubmatrix_eigenvalues_interlace"
label = "Eigenvalues of a principal submatrix interlace"
headline = true
symcat = "cauchyInterlacingTheorem"

[[theorems]]
name = "RealRooted.Challenges.CauchyInterlacing.principalSubmatrix_charpoly_interlaces"
label = "Characteristic polynomials of a principal submatrix interlace"

[[theorems]]
name = "RealRooted.sortedEigenvalues_add_vecMulVec_succ_le"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: eigenvalues of A + vv* are at most the previous eigenvalues of A"

[[theorems]]
name = "RealRooted.sortedEigenvalues_le_add_vecMulVec"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: rank-one updates raise eigenvalues"

[[theorems]]
name = "RealRooted.charpoly_strictInterl_add_vecMulVec"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: characteristic polynomials of A and A + vvᵀ interlace"
-->

<!-- realrooted-catalog-content -->
# Cauchy interlacing

The eigenvalues of a Hermitian matrix and of any principal submatrix of one smaller size
interlace, and so do the characteristic polynomials in the real symmetric case.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.

**Theorem (Cauchy).** Let $A$ be a Hermitian $(n+1)\times(n+1)$ matrix over $\mathbb R$ or
$\mathbb C$ with eigenvalues $\lambda_0\ge\dots\ge\lambda_n$. Let $A'$ be obtained by deleting
the $i$-th row and column, with eigenvalues $\mu_0\ge\dots\ge\mu_{n-1}$. Then
$$
\lambda_{k+1}\le\mu_k\le\lambda_k\qquad(0\le k<n).
$$
If $A$ is real symmetric, then $\chi_{A'}\ll\chi_A$ for the characteristic polynomials.

**Theorem (Weyl, rank-one update).** Let $A$ be an $N\times N$ Hermitian matrix and $v$ a vector,
with eigenvalues of $A$ and $B=A+vv^*$ listed in decreasing order. Then
$\lambda_k(A)\le\lambda_k(B)$ for all $k$, and $\lambda_k(B)\le\lambda_{k-1}(A)$ for $k\ge1$. If
$A$ is real symmetric and $v$ is real, then $\chi_A\ll\chi_{A+vv^T}$.

## Proof

Both statements follow from the [Courant–Fischer theorem](/RealRooted/theorems/courant-fischer/).

## References

See [@Godsil2017; @Fisk2005x] and the
[Cauchy interlacing entry on symmetricfunctions.com](sf:cauchyInterlacingTheorem).
<!-- /realrooted-catalog-content -->

Human statement:
sf:cauchyInterlacingTheorem

References used by the catalog:

* C. D. Godsil, "Algebraic Combinatorics", Routledge, 2017.
* S. Fisk, "A very short proof of Cauchy's interlace theorem for eigenvalues
  of Hermitian matrices", Amer. Math. Monthly 112 (2005), 118.

This module records the eigenvalue and characteristic-polynomial forms; Weyl's
rank-one interlacing is in `RealRooted.CauchyInterlacing.RankOne`.
-/

public section

open Matrix Polynomial

namespace RealRooted
namespace Challenges
namespace CauchyInterlacing

/-- Cauchy's interlacing theorem in principal-submatrix form: the eigenvalues
of the one-index principal submatrix interlace the eigenvalues of the original
Hermitian matrix. -/
theorem principalSubmatrix_eigenvalues_interlace
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    RealRooted.Interlace
      (RealRooted.sortedEigenvalues
        (A.submatrix i.succAbove i.succAbove) (hA.submatrix i.succAbove))
      (RealRooted.sortedEigenvalues A hA) :=
  RealRooted.cauchy_interlacing 𝕜 A hA i

/-- Cauchy interlacing for characteristic polynomials. -/
theorem principalSubmatrix_charpoly_interlaces {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    Interlaces (A.submatrix i.succAbove i.succAbove).charpoly A.charpoly :=
  RealRooted.principalSubmatrix_charpoly_interlaces A hA i

end CauchyInterlacing
end Challenges
end RealRooted
