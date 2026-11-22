/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power interpolation for nonnegative bounds

The minimum of two nonnegative bounds is bounded by their weighted geometric
mean. A logarithm can be absorbed into an arbitrarily small positive power.
-/

public section

namespace Real

/-- A weighted geometric mean of two nonnegative reals dominates their minimum. -/
theorem min_le_rpow_one_sub_mul_rpow {a b p : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    min a b ≤ a ^ (1 - p) * b ^ p := by
  have hm : 0 ≤ min a b := le_min ha hb
  calc
    min a b = (min a b) ^ (1 - p) * (min a b) ^ p := by
      rw [← rpow_add' hm (by linarith : 1 - p + p ≠ 0)]
      simp
    _ ≤ a ^ (1 - p) * b ^ p :=
      mul_le_mul (rpow_le_rpow hm (min_le_left _ _) (sub_nonneg.mpr hp1))
        (rpow_le_rpow hm (min_le_right _ _) hp0)
        (rpow_nonneg hm p) (rpow_nonneg ha (1 - p))

/-- Uniformly on the real line, `log (2 + |t|)` is bounded by any positive power of `1 + |t|`. -/
theorem log_two_add_abs_le_mul_rpow {r : ℝ} (hr : 0 < r) (t : ℝ) :
    log (2 + |t|) ≤ (2 ^ r / r) * (1 + |t|) ^ r := by
  calc
    log (2 + |t|) ≤ (2 + |t|) ^ r / r := log_le_rpow_div (by positivity) hr
    _ ≤ (2 * (1 + |t|)) ^ r / r :=
      div_le_div_of_nonneg_right
        (rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hr.le) hr.le
    _ = (2 ^ r / r) * (1 + |t|) ^ r := by
      rw [mul_rpow (by norm_num) (by positivity)]
      ring

end Real
