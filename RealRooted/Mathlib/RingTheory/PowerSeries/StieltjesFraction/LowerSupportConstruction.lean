/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportParameters
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ActivePrefix

/-!
# Construction of nonnegative lower-support parameters

The same recurrence works at shift zero. A denominator can vanish only at
an inactive numerator; matching the active prefix suffices for equality of
the formal fractions. Thus no standardized inactive-tail constraint is used.
-/

public section

namespace PowerSeries

/-- The even parameters for a translated Stieltjes fraction. -/
@[expose] noncomputable def stieltjesShiftParameters (c : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 + stieltjesShiftParameters c a k) * a (2 * k + 1) /
      (c * (1 + stieltjesShiftParameters c a k) + a (2 * k))

/-- All constructed even parameters are nonnegative, including at shift zero. -/
theorem stieltjesShiftParameters_nonneg {c : ℝ} (hc : 0 ≤ c) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) (n : ℕ) : 0 ≤ stieltjesShiftParameters c a n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact div_nonneg (mul_nonneg (by positivity) (ha _))
        (add_nonneg (mul_nonneg hc (by positivity)) (ha _))

/-- The recurrence recovers every odd numerator whose preceding even numerator is nonzero. -/
theorem stieltjesNumeratorsBeforeShift_parameters_odd {c : ℝ} (hc : 0 ≤ c)
    {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (k : ℕ) (hk : a (2 * k) ≠ 0) :
    stieltjesNumeratorsBeforeShift c (stieltjesShiftParameters c a)
      (fun j => a (2 * j)) (2 * k + 1) = a (2 * k + 1) := by
  have hu := stieltjesShiftParameters_nonneg hc ha k
  have h1 : 1 + stieltjesShiftParameters c a k ≠ 0 := by positivity
  have hD : c * (1 + stieltjesShiftParameters c a k) + a (2 * k) ≠ 0 := by
    apply ne_of_gt
    exact add_pos_of_nonneg_of_pos (mul_nonneg hc (by positivity))
      (lt_of_le_of_ne (ha _) (Ne.symm hk))
  rw [stieltjesNumeratorsBeforeShift_odd, stieltjesShiftParameters]
  rw [div_mul_cancel₀ _ hD, mul_div_cancel_left₀ _ h1]

/-- Before translation the constructed data agree with the original formal
fraction, even when arbitrary inactive numerators follow the first zero. -/
theorem stieltjesTail_beforeShift_parameters {c : ℝ} (hc : 0 ≤ c) {a : ℕ → ℝ}
    (ha : ∀ k, 0 ≤ a k) :
    stieltjesTail a 0 =
      stieltjesTail (stieltjesNumeratorsBeforeShift c (stieltjesShiftParameters c a)
        (fun j => a (2 * j))) 0 := by
  apply stieltjesTail_eq_of_active_prefix
  intro n hn
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst n
    simp
  · subst n
    exact (stieltjesNumeratorsBeforeShift_parameters_odd hc ha k
      (hn (2 * k) (by lia))).symm

/-- Every nonnegative Stieltjes fraction acquires nonnegative lower-support
parameters under a nonnegative binomial translation. -/
theorem exists_parameters_binomialTransform_stieltjesTail {c : ℝ} (hc : 0 ≤ c)
    {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) :
    ∃ u v : ℕ → ℝ, u 0 = 0 ∧ (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧
      binomialTransform c (stieltjesTail a 0) =
        stieltjesTail (shiftedStieltjesNumerators c u v) 0 := by
  refine ⟨stieltjesShiftParameters c a, fun k => a (2 * k), rfl,
    stieltjesShiftParameters_nonneg hc ha, fun k => ha _, ?_⟩
  rw [stieltjesTail_beforeShift_parameters hc ha]
  exact binomialTransform_beforeShift (stieltjesShiftParameters_nonneg hc ha) rfl

end PowerSeries
