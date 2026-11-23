module

public import RealRooted.Hermite.FormalDifferential.Basic
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Mathlib.RingTheory.PowerSeries.LowDegree
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# A quadratic obstruction to eventual real-rootedness

A formal real symbol with constant coefficient one and nonnegative second
cumulant fails to make `X^2 + 1` real-rooted at every iterate. This is the
necessity mechanism in the polynomial classification of Kim--Kim (2015).
The zero-constant branch is handled separately by finite annihilation.
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- Exact completed-square evaluation of all iterates on `X^2 + 1`. -/
theorem eval_iterate_formalDifferentialOperator_X_sq_add_one
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ = 1) (m : ℕ) (x : ℝ) :
    ((formalDifferentialOperator φ)^[m] (X ^ 2 + 1)).eval x =
      (x + (m : ℝ) * PowerSeries.coeff 1 φ) ^ 2 + 1 +
        (m : ℝ) * (2 * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2) := by
  have hP : IsMonicOfDegree (X ^ 2 + 1 : ℝ[X]) 2 :=
    (isMonicOfDegree_X_pow ℝ 2).add_right (by simp)
  rw [← formalDifferentialOperator_pow, formalDifferentialOperator_eq_sum,
    hP.natDegree_eq]
  norm_num [Finset.sum_range_succ, Function.iterate_succ_apply',
    PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_one_pow,
    PowerSeries.coeff_two_pow_of_constantCoeff_eq_one h0, h0, Nat.cast_choose_two]
  ring

/-- The normalized obstruction also retains degree two at every iterate. -/
private theorem not_splits_normalized_iterates
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ = 1)
    (hvariance : 0 ≤ 2 * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2)
    (m : ℕ) :
    ¬ ((formalDifferentialOperator φ)^[m] (X ^ 2 + 1)).Splits := by
  let P : ℝ[X] := X ^ 2 + 1
  have hP : IsMonicOfDegree P 2 :=
    (isMonicOfDegree_X_pow ℝ 2).add_right (by simp)
  have hc : ((φ ^ m).trunc (P.natDegree + 1)).coeff 0 = 1 := by
    simp [PowerSeries.coeff_trunc, PowerSeries.coeff_zero_eq_constantCoeff, h0]
  have hmonic : (formalDifferentialOperator (φ ^ m) P).Monic :=
    applyAsDifferentialOperator_monic hc hP.monic
  have hdegree : (formalDifferentialOperator (φ ^ m) P).degree ≠ 0 := by
    rw [degree_eq_natDegree hmonic.ne_zero]
    change ((applyAsDifferentialOperator _ P).natDegree : WithBot ℕ) ≠ 0
    rw [natDegree_applyAsDifferentialOperator hc hP.monic, hP.natDegree_eq]
    norm_num
  intro hsplit
  rw [← formalDifferentialOperator_pow] at hsplit
  obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero hdegree
  have heval := eval_iterate_formalDifferentialOperator_X_sq_add_one h0 m x
  rw [← formalDifferentialOperator_pow] at heval
  have hnonneg : 0 ≤ (m : ℝ) *
      (2 * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2) :=
    mul_nonneg (Nat.cast_nonneg m) hvariance
  have hsquare := sq_nonneg (x + (m : ℝ) * PowerSeries.coeff 1 φ)
  change (formalDifferentialOperator (φ ^ m) (X ^ 2 + 1)).eval x = 0 at hx
  linarith

/-- A nonzero constant coefficient and nonnegative second cumulant prevent
every iterate of `X^2 + 1` from splitting. No convergence of the symbol is assumed. -/
theorem not_splits_iterate_formalDifferentialOperator_X_sq_add_one
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ ≠ 0)
    (hvariance : 0 ≤ 2 * PowerSeries.constantCoeff φ * PowerSeries.coeff 2 φ -
      PowerSeries.coeff 1 φ ^ 2) (m : ℕ) :
    ¬ ((formalDifferentialOperator φ)^[m] (X ^ 2 + 1)).Splits := by
  let a : ℝ := PowerSeries.constantCoeff φ
  let ψ : PowerSeries ℝ := PowerSeries.C a⁻¹ * φ
  have ha : a ≠ 0 := h0
  have hψ0 : PowerSeries.constantCoeff ψ = 1 := by simp [ψ, a, h0]
  have hcoeff (k : ℕ) : PowerSeries.coeff k ψ = a⁻¹ * PowerSeries.coeff k φ := by
    simp [ψ]
  have hψvar : 0 ≤ 2 * PowerSeries.coeff 2 ψ - PowerSeries.coeff 1 ψ ^ 2 := by
    rw [hcoeff, hcoeff]
    have heq : 2 * (a⁻¹ * PowerSeries.coeff 2 φ) -
        (a⁻¹ * PowerSeries.coeff 1 φ) ^ 2 =
        (2 * a * PowerSeries.coeff 2 φ - PowerSeries.coeff 1 φ ^ 2) / a ^ 2 := by
      field_simp [ha]
    rw [heq]
    exact div_nonneg hvariance (sq_nonneg a)
  have hpower : ψ ^ m = PowerSeries.C (a⁻¹ ^ m) * φ ^ m := by
    simp only [ψ, mul_pow, map_pow]
  intro hsplit
  apply not_splits_normalized_iterates hψ0 hψvar m
  rw [← formalDifferentialOperator_pow, hpower, formalDifferentialOperator_C_mul]
  rw [← formalDifferentialOperator_pow] at hsplit
  exact hsplit.C_mul _

end RealRooted.HermitePoulain
