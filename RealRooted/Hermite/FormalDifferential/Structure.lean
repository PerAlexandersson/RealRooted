module

public import RealRooted.Hermite.FormalDifferential.Basic
import RealRooted.Hermite.FormalDifferential.OperatorLimits
import RealRooted.Hermite.PoulainSymbolInterlacing
import Mathlib.Tactic.Linarith

/-!
# Degree and scalar behavior of formal differential operators
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- The zero polynomial is annihilated by every formal differential symbol. -/
@[simp] theorem formalDifferentialOperator_zero (φ : PowerSeries ℝ) :
    formalDifferentialOperator φ 0 = 0 := by
  simp [formalDifferentialOperator]

/-- A nonzero constant term preserves the degree of a nonzero polynomial input. -/
theorem natDegree_formalDifferentialOperator {φ : PowerSeries ℝ}
    (hφ : PowerSeries.constantCoeff φ ≠ 0) {P : ℝ[X]} (hP : P ≠ 0) :
    (formalDifferentialOperator φ P).natDegree = P.natDegree := by
  apply natDegree_applyAsDifferentialOperator_of_coeff_zero_ne_zero _ hP
  simpa only [PowerSeries.coeff_trunc, ite_eq_left (Nat.zero_lt_succ _),
    PowerSeries.coeff_zero_eq_constantCoeff] using hφ

/-- A constant-one formal differential symbol preserves monicity. -/
theorem formalDifferentialOperator_monic {φ : PowerSeries ℝ}
    (hφ : PowerSeries.constantCoeff φ = 1) {P : ℝ[X]} (hP : P.Monic) :
    (formalDifferentialOperator φ P).Monic := by
  apply applyAsDifferentialOperator_monic _ hP
  simpa only [PowerSeries.coeff_trunc, ite_eq_left (Nat.zero_lt_succ _),
    PowerSeries.coeff_zero_eq_constantCoeff] using hφ

/-- Scalars in the input commute with the formal differential action. -/
theorem formalDifferentialOperator_mul_input (φ : PowerSeries ℝ) (a : ℝ) (P : ℝ[X]) :
    formalDifferentialOperator φ (C a * P) = C a * formalDifferentialOperator φ P := by
  rw [formalDifferentialOperator_eq_sum_of_natDegree_le φ (natDegree_C_mul_le a P),
    formalDifferentialOperator_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [iterate_derivative_C_mul]
  exact mul_left_comm _ _ _

end RealRooted.HermitePoulain
