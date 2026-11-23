/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# A factorial bound retaining the exponential scale

The elementary upper bound supplied by the decreasing Stirling sequence
cancels the exponential factor in optimized Gaussian Cauchy estimates.
-/

public section

namespace Real

/-- A coarse global upper Stirling bound, sufficient to retain the exact
exponential scale. Only a polynomial prefactor is lost. -/
private theorem factorial_le_two_exp_mul {n : ℕ} (hn : n ≠ 0) :
    (n.factorial : ℝ) ≤ 2 * exp 1 * n * ((n : ℝ) / exp 1) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hs := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  change Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 at hs
  rw [Stirling.stirlingSeq_one] at hs
  have he : exp 1 / sqrt 2 ≤ exp 1 := by
    apply (div_le_iff₀ (sqrt_pos.mpr (by norm_num))).mpr
    nlinarith [exp_pos 1, (one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2))]
  have hupper := hs.trans he
  rw [Stirling.stirlingSeq, div_le_iff₀ (by positivity)] at hupper
  have hsqrt : sqrt (2 * ((m + 1 : ℕ) : ℝ)) ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
    exact sqrt_le_self_iff.mpr (Or.inr (by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [Nat.cast_add, Nat.cast_one]
      linarith))
  calc
    _ ≤ exp 1 * (sqrt (2 * ((m + 1 : ℕ) : ℝ)) *
        (((m + 1 : ℕ) : ℝ) / exp 1) ^ (m + 1)) := hupper
    _ ≤ exp 1 * (2 * ((m + 1 : ℕ) : ℝ) *
        (((m + 1 : ℕ) : ℝ) / exp 1) ^ (m + 1)) := by gcongr
    _ = _ := by simp only [Nat.succ_eq_add_one]; ring

/-- The normalized factorial grows at most linearly. This includes `n=0`
and uses `n+1` so every denominator is strictly positive. -/
theorem factorial_mul_exp_div_pow_le (n : ℕ) :
    (n.factorial : ℝ) * (exp 1 / ((n : ℝ) + 1)) ^ n ≤
      2 * exp 1 * ((n : ℝ) + 1) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, zero_add, pow_zero,
      mul_one]
    nlinarith [one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  · have hp : ((n : ℝ) / ((n : ℝ) + 1)) ^ n ≤ 1 :=
      pow_le_one₀ (by positivity) ((div_le_iff₀ (by positivity)).mpr (by linarith))
    calc
      _ ≤ (2 * exp 1 * n * ((n : ℝ) / exp 1) ^ n) *
          (exp 1 / ((n : ℝ) + 1)) ^ n :=
        mul_le_mul_of_nonneg_right (factorial_le_two_exp_mul hn) (by positivity)
      _ = 2 * exp 1 * n * ((n : ℝ) / ((n : ℝ) + 1)) ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        field_simp
      _ ≤ 2 * exp 1 * n := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * exp 1 * (n : ℝ))
      _ ≤ _ := by nlinarith [exp_pos 1]

end Real
