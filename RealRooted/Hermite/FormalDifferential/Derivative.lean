module

public import RealRooted.Hermite.FormalDifferential.Basic
import RealRooted.Hermite.FormalDifferential.Composition

/-!
# Derivative commutation for formal polynomial operators
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- A monomial formal symbol acts by the corresponding iterated derivative. -/
theorem formalDifferentialOperator_X_pow (n : ℕ) (P : ℝ[X]) :
    formalDifferentialOperator (PowerSeries.X ^ n) P = (derivative^[n]) P := by
  have hcoe : (PowerSeries.X ^ n : PowerSeries ℝ) = ((X ^ n : ℝ[X]) : PowerSeries ℝ) := by
    simp
  rw [hcoe, formalDifferentialOperator_coe]
  simpa only [mul_one, applyAsDifferentialOperator_one] using
    applyAsDifferentialOperator_X_pow_mul n 1 P

/-- All iterated polynomial derivatives commute with a formal differential operator. -/
theorem iterate_derivative_formalDifferentialOperator
    (φ : PowerSeries ℝ) (P : ℝ[X]) (n : ℕ) :
    (derivative^[n]) (formalDifferentialOperator φ P) =
      formalDifferentialOperator φ ((derivative^[n]) P) := by
  rw [← formalDifferentialOperator_X_pow, ← formalDifferentialOperator_mul,
    mul_comm (PowerSeries.X ^ n) φ, formalDifferentialOperator_mul,
    formalDifferentialOperator_X_pow]

end RealRooted.HermitePoulain
