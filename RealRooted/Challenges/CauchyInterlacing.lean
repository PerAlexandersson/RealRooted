import RealRooted.CauchyInterlacing

/-!
# Cauchy interlacing challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#cauchyInterlacingTheorem

References used by the catalog:

* C. D. Godsil, "Algebraic Combinatorics", Routledge, 2017.
* S. Fisk, "A very short proof of Cauchy's interlace theorem for eigenvalues
  of Hermitian matrices", Amer. Math. Monthly 112 (2005), 118.

This module exposes the completed eigenvalue form of Cauchy's interlacing
theorem for Hermitian matrices.  The Courant--Fischer proof and spectral API
remain in `RealRooted.CauchyInterlacing`.
-/

namespace RealRooted
namespace Challenges
namespace CauchyInterlacing

/-- Challenge-facing name for interlacing of ordered eigenvalue lists. -/
abbrev EigenvalueInterlaces {n : ℕ} (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) :
    Prop :=
  RealRooted.Interlace μ lam

/-- Challenge-facing name for the sorted eigenvalues of a Hermitian matrix. -/
noncomputable abbrev OrderedEigenvalues {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) : Fin N → ℝ :=
  RealRooted.sortedEigenvalues A hA

/-- Challenge-facing name for deleting one row and column from a matrix. -/
noncomputable abbrev PrincipalSubmatrix {𝕜 : Type*} {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  A.submatrix i.succAbove i.succAbove

/-- Cauchy's eigenvalue interlacing theorem for Hermitian matrices. -/
theorem eigenvalues_interlace (𝕜 : Type*) [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (hA : A.IsHermitian)
    (i : Fin (n + 1)) :
    RealRooted.Interlace
      (RealRooted.sortedEigenvalues (A.submatrix i.succAbove i.succAbove)
        (hA.submatrix i.succAbove))
      (RealRooted.sortedEigenvalues A hA) :=
  RealRooted.cauchy_interlacing 𝕜 A hA i

/-- Cauchy's interlacing theorem in principal-submatrix form: the eigenvalues
of the one-index principal submatrix interlace the eigenvalues of the original
Hermitian matrix. -/
theorem principalSubmatrix_eigenvalues_interlace
    {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)
    (hA : A.IsHermitian) (i : Fin (n + 1)) :
    EigenvalueInterlaces
      (OrderedEigenvalues
        (PrincipalSubmatrix A i) (hA.submatrix i.succAbove))
      (OrderedEigenvalues A hA) :=
  theoremStatement 𝕜 A hA i

end CauchyInterlacing
end Challenges
end RealRooted
