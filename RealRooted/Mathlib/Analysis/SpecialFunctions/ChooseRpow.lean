/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Binomial coefficients under real-power normalization
-/

public section

open Filter Topology

namespace Nat

/-- The critical real-power normalization of a fixed binomial coefficient. -/
theorem tendsto_choose_mul_rpow_atTop (k : ℕ) :
    Tendsto (fun m : ℕ ↦ (m.choose k : ℝ) * (m : ℝ) ^ (-(k : ℝ))) atTop
      (𝓝 (1 / (k.factorial : ℝ))) := by
  have heq (m : ℕ) : ((m : ℝ)⁻¹) ^ k = (m : ℝ) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (Nat.cast_nonneg m), Real.rpow_natCast, inv_pow]
  simpa only [heq] using tendsto_choose_mul_inv_pow_atTop k

/-- A larger real-power normalization makes a fixed binomial coefficient vanish. -/
theorem tendsto_choose_mul_rpow_atTop_of_lt (k : ℕ) {u : ℝ} (hu : (k : ℝ) < u) :
    Tendsto (fun m : ℕ ↦ (m.choose k : ℝ) * (m : ℝ) ^ (-u)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (-(u - k))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hu)).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_choose_mul_rpow_atTop k).mul hpow
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by lia)
  rw [mul_assoc, ← Real.rpow_add hm0]
  congr 2
  ring

end Nat
