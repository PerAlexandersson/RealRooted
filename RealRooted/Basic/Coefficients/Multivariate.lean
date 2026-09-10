import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Tactic.FinCases
import RealRooted.Basic.Coefficients
import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative

/-!
# Univariate bridges for nonnegative multivariate coefficients

This file connects coefficientwise nonnegativity for multivariate and
univariate polynomials and records its compatibility with homogenization.
-/

open Polynomial

namespace MvPolynomial.HasNonnegCoeffs

/-- The unique-variable equivalence preserves coefficientwise
nonnegativity. -/
theorem uniqueAlgEquiv {σ : Type*} [Unique σ] {P : MvPolynomial σ ℝ}
    (hP : MvPolynomial.HasNonnegCoeffs P) :
    RealRooted.HasNonnegCoeffs (MvPolynomial.uniqueAlgEquiv ℝ σ P) := by
  intro n
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  exact hP _

/-- Evaluating a bivariate polynomial at `(X, 1)` preserves coefficientwise
nonnegativity. -/
theorem aeval_X_one {P : MvPolynomial (Fin 2) ℝ}
    (hP : MvPolynomial.HasNonnegCoeffs P) :
    RealRooted.HasNonnegCoeffs
      (MvPolynomial.aeval ![Polynomial.X, 1] P) := by
  let Q : MvPolynomial (Fin 1) ℝ :=
    MvPolynomial.aeval ![MvPolynomial.X 0, 1] P
  have hQ : MvPolynomial.HasNonnegCoeffs Q := by
    apply hP.aeval
    intro i
    fin_cases i
    · exact MvPolynomial.HasNonnegCoeffs.X 0
    · exact MvPolynomial.HasNonnegCoeffs.one
  have heq : MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) Q =
      MvPolynomial.aeval ![Polynomial.X, 1] P := by
    dsimp only [Q]
    change (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toAlgHom
        (MvPolynomial.aeval ![MvPolynomial.X 0, 1] P) = _
    rw [MvPolynomial.comp_aeval_apply]
    congr 1
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  rw [← heq]
  exact hQ.uniqueAlgEquiv

end MvPolynomial.HasNonnegCoeffs

namespace RealRooted.HasNonnegCoeffs

/-- Homogenization preserves coefficientwise nonnegativity. -/
theorem homogenize {p : ℝ[X]} (hp : RealRooted.HasNonnegCoeffs p) (d : ℕ) :
    MvPolynomial.HasNonnegCoeffs (p.homogenize d) := by
  intro m
  rw [Polynomial.coeff_homogenize]
  split
  · exact hp _
  · exact le_rfl

end RealRooted.HasNonnegCoeffs
