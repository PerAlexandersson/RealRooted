import RealRooted.CauchyInterlacing.Polynomial
import RealRooted.CauchyInterlacing.RankOne

/-!
# Cauchy interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "cauchy-interlacing"
authors = ["Fisk"]
years = [2005]

[[theorems]]
name = "RealRooted.Challenges.CauchyInterlacing.principalSubmatrix_eigenvalues_interlace"
label = "Eigenvalues of a principal submatrix interlace"

[[theorems]]
name = "RealRooted.Challenges.CauchyInterlacing.principalSubmatrix_charpoly_interlaces"
label = "Characteristic polynomials of a principal submatrix interlace"

[[theorems]]
name = "RealRooted.sortedEigenvalues_add_vecMulVec_succ_le"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: eigenvalues of a rank-one update interlace"

[[theorems]]
name = "RealRooted.charpoly_strictInterl_add_vecMulVec"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: characteristic polynomials of A and A + vvᵀ interlace"
-->

<!-- realrooted-catalog-content -->
# Cauchy interlacing

List the eigenvalues of a Hermitian $(n+1) \times (n+1)$ matrix as
$\lambda_0 \geq \dotsb \geq \lambda_n$, and those of a principal submatrix of size
$n$ as $\mu_0 \geq \dotsb \geq \mu_{n-1}$. Then the eigenvalues interlace:
$\lambda_{k+1} \leq \mu_k \leq \lambda_k$ for every $k$. For real symmetric
matrices, the corresponding characteristic polynomials also interlace.

Weyl's companion result concerns rank-one updates: the eigenvalues of
$A + vv^*$ satisfy $\lambda_k(A) \leq \lambda_k(A + vv^*) \leq \lambda_{k-1}(A)$, so the
characteristic polynomials of $A$ and $A + vv^{T}$ interlace.  Both results follow
from the Courant–Fischer min-max principle.

## References

C. D. Godsil, *Algebraic Combinatorics*, Routledge, 2017; and S. Fisk,
“A very short proof of Cauchy’s interlace theorem for eigenvalues of Hermitian
matrices,” *American Mathematical Monthly* 112 (2005), 118.  See also the
[Cauchy interlacing entry on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#cauchyInterlacingTheorem).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#cauchyInterlacingTheorem

References used by the catalog:

* C. D. Godsil, "Algebraic Combinatorics", Routledge, 2017.
* S. Fisk, "A very short proof of Cauchy's interlace theorem for eigenvalues
  of Hermitian matrices", Amer. Math. Monthly 112 (2005), 118.

This module records the eigenvalue and characteristic-polynomial forms; Weyl's
rank-one interlacing is in `RealRooted.CauchyInterlacing.RankOne`.
-/

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
