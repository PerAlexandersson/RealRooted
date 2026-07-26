module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-!
# Trigonometric sign helpers

This file contains small upstream-shaped trigonometric lemmas used by
RealRooted.
-/

public section

noncomputable section

namespace Real

/-- The sine function is nonpositive on the interval `[π, 2π]`. -/
lemma sin_nonpos_of_pi_le_of_le_two_pi {x : ℝ} (hpi : π ≤ x)
    (h2pi : x ≤ 2 * π) : sin x ≤ 0 := by
  have hy_nonneg : 0 ≤ 2 * π - x := by linarith
  have hy_le_pi : 2 * π - x ≤ π := by linarith
  have hy_sin_nonneg : 0 ≤ sin (2 * π - x) :=
    sin_nonneg_of_nonneg_of_le_pi hy_nonneg hy_le_pi
  rw [sin_two_pi_sub] at hy_sin_nonneg
  linarith

/-- On the interval `[kπ, (k + 1)π]`, sine is nonnegative when `k` is even. -/
lemma sin_nonneg_of_even_nat_mul_pi_le_of_le_succ_nat_mul_pi {k : ℕ} {x : ℝ}
    (hk : Even k) (hlo : (k : ℝ) * π ≤ x)
    (hhi : x ≤ ((k + 1 : ℕ) : ℝ) * π) : 0 ≤ sin x := by
  have hy0 : 0 ≤ x - (k : ℝ) * π := by linarith
  have hypi : x - (k : ℝ) * π ≤ π := by
    have hsucc : ((k + 1 : ℕ) : ℝ) * π = (k : ℝ) * π + π := by
      norm_num [Nat.cast_add]
      ring
    nlinarith
  have hy : 0 ≤ sin (x - (k : ℝ) * π) :=
    sin_nonneg_of_nonneg_of_le_pi hy0 hypi
  rw [sin_sub_nat_mul_pi] at hy
  simpa [hk.neg_one_pow] using hy

/-- On the interval `[kπ, (k + 1)π]`, sine is nonpositive when `k` is odd. -/
lemma sin_nonpos_of_odd_nat_mul_pi_le_of_le_succ_nat_mul_pi {k : ℕ} {x : ℝ}
    (hk : Odd k) (hlo : (k : ℝ) * π ≤ x)
    (hhi : x ≤ ((k + 1 : ℕ) : ℝ) * π) : sin x ≤ 0 := by
  have hy0 : 0 ≤ x - (k : ℝ) * π := by linarith
  have hypi : x - (k : ℝ) * π ≤ π := by
    have hsucc : ((k + 1 : ℕ) : ℝ) * π = (k : ℝ) * π + π := by
      norm_num [Nat.cast_add]
      ring
    nlinarith
  have hy : 0 ≤ sin (x - (k : ℝ) * π) :=
    sin_nonneg_of_nonneg_of_le_pi hy0 hypi
  rw [sin_sub_nat_mul_pi] at hy
  simpa [hk.neg_one_pow] using hy

end Real
