/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianDerivative
import Mathlib.Analysis.Complex.Liouville

/-!
# Gaussian bounds for all spatial derivatives
-/

public section

namespace Complex

/-- Every derivative retains any strictly larger Gaussian coefficient.
A fixed positive Cauchy radius gives an explicit derivative-dependent constant. -/
theorem norm_iteratedDeriv_le_exp_sq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M b d : ℝ} (hM : 0 ≤ M) (hb : 0 ≤ b) (hbd : b < d)
    (hbound : ∀ w, ‖f w‖ ≤ M * Real.exp (b * ‖w‖ ^ 2)) (n : ℕ) (z : ℂ) :
    ‖iteratedDeriv n f z‖ ≤
      (n.factorial * M * Real.exp (b + b ^ 2 / (d - b))) *
        Real.exp (d * ‖z‖ ^ 2) := by
  let E : ℝ := b + b ^ 2 / (d - b)
  have hcircle : ∀ w ∈ Metric.sphere z 1,
      ‖f w‖ ≤ M * Real.exp E * Real.exp (d * ‖z‖ ^ 2) := by
    intro w hw
    have hwz : ‖w - z‖ = 1 := mem_sphere_iff_norm.mp hw
    have htri : ‖w‖ ≤ ‖z‖ + 1 := by
      calc
        _ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        _ = _ := by rw [hwz, add_comm]
    have he : b * ‖w‖ ^ 2 ≤ d * ‖z‖ ^ 2 + E := by
      calc
        _ ≤ b * (‖z‖ + 1) ^ 2 := by gcongr
        _ ≤ _ := by
          simpa only [one_pow, mul_one] using
            (Real.mul_add_sq_le_of_lt (r := ‖z‖) (t := 1) hbd)
    calc
      _ ≤ M * Real.exp (b * ‖w‖ ^ 2) := hbound w
      _ ≤ M * Real.exp (d * ‖z‖ ^ 2 + E) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hM
      _ = _ := by rw [Real.exp_add]; ring
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (show (0 : ℝ) < 1 from zero_lt_one) hf.diffContOnCl hcircle
  calc
    _ ≤ n.factorial * (M * Real.exp E * Real.exp (d * ‖z‖ ^ 2)) := by
      simpa only [one_pow, div_one] using h
    _ = _ := by dsimp only [E]; ring

end Complex
