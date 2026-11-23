/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianUniformBound
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.OfBound

/-!
# Gaussian growth of the actual infinite differential image
-/

public section

namespace Complex

/-- Under the strict Gaussian threshold, the actual differential image has
a global Gaussian bound. Its Gaussian coefficient need not equal that of the input. -/
theorem exists_norm_infiniteDifferentialApply_le_exp_sq {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    ∃ M > 0, ∃ E > 0, ∀ z,
      ‖infiniteDifferentialApply φ f z‖ ≤ M * Real.exp (E * ‖z‖ ^ 2) := by
  obtain ⟨E, hE, B, _, hs, hB⟩ := exists_gaussian_differential_majorant
    hf hMφ hMf ha hb hab hfbound
  refine ⟨max 1 (∑' n, B n), lt_of_lt_of_le zero_lt_one (le_max_left _ _), E, hE, ?_⟩
  intro z
  have hsum := hs.mul_right (Real.exp (E * ‖z‖ ^ 2))
  have hnorm : Summable (fun n : ℕ ↦
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (hB φ hφ hφbound · z) hsum
  calc
    _ ≤ ∑' n : ℕ, ‖iteratedDeriv n φ 0 * iteratedDeriv n f z /
        (n.factorial : ℂ)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, B n * Real.exp (E * ‖z‖ ^ 2) :=
      hnorm.tsum_le_tsum (hB φ hφ hφbound · z) hsum
    _ = (∑' n, B n) * Real.exp (E * ‖z‖ ^ 2) := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- The strict Gaussian threshold gives order at most two for the actual
differential image, including zero output. -/
theorem orderLE_infiniteDifferentialApply_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    TauCeti.OrderLE (infiniteDifferentialApply φ f) 2 := by
  obtain ⟨M, _, E, _, hbound⟩ := exists_norm_infiniteDifferentialApply_le_exp_sq
    hφ hf hMφ hMf ha hb hab hφbound hfbound
  apply TauCeti.orderLE_of_norm_le_mul_exp_rpow (B := M) (C := E)
  intro z
  simpa only [Real.rpow_two] using hbound z

end Complex
