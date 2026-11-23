/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville

/-!
# Gaussian bounds at arbitrary Cauchy centers

Changing the center increases the quadratic coefficient by an arbitrarily
small positive amount. The Cauchy radius uses `n+1` and is never zero.
-/

public section

namespace Real

/-- Young's inequality with the coefficient arranged for recentering a
Gaussian norm bound. -/
theorem mul_add_sq_le_of_lt {b d r t : ℝ} (hbd : b < d) :
    b * (r + t) ^ 2 ≤ d * r ^ 2 + (b + b ^ 2 / (d - b)) * t ^ 2 := by
  have hdelta : 0 < d - b := sub_pos.mpr hbd
  have hsq := sq_nonneg ((d - b) * r - b * t)
  have heq : (d - b) *
      (d * r ^ 2 + (b + b ^ 2 / (d - b)) * t ^ 2 - b * (r + t) ^ 2) =
      ((d - b) * r - b * t) ^ 2 := by
    field_simp [hdelta.ne']
    ring
  have hnonneg : 0 ≤ d * r ^ 2 + (b + b ^ 2 / (d - b)) * t ^ 2 -
      b * (r + t) ^ 2 := by
    exact (mul_nonneg_iff_of_pos_left hdelta).mp (heq.symm ▸ hsq)
  linarith

end Real

namespace Complex

/-- Recenter a global Gaussian norm bound, retaining any strictly larger
quadratic coefficient. The spatial constant is explicit. -/
theorem norm_le_gaussian_center {f : ℂ → ℂ} {M b d : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hbd : b < d)
    (hbound : ∀ w, ‖f w‖ ≤ M * Real.exp (b * ‖w‖ ^ 2)) (z w : ℂ) :
    ‖f w‖ ≤ (M * Real.exp ((b + b ^ 2 / (d - b)) * ‖z‖ ^ 2)) *
      Real.exp (d * ‖w - z‖ ^ 2) := by
  have htri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (w - z) z
  have hsq : b * ‖w‖ ^ 2 ≤
      d * ‖w - z‖ ^ 2 + (b + b ^ 2 / (d - b)) * ‖z‖ ^ 2 := by
    calc
      _ ≤ b * (‖w - z‖ + ‖z‖) ^ 2 := by gcongr
      _ ≤ _ := Real.mul_add_sq_le_of_lt hbd
  calc
    _ ≤ M * Real.exp (b * ‖w‖ ^ 2) := hbound w
    _ ≤ M * Real.exp
        (d * ‖w - z‖ ^ 2 + (b + b ^ 2 / (d - b)) * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq) hM
    _ = _ := by rw [Real.exp_add]; ring

/-- An optimized positive Cauchy radius bounds all derivatives under a
Gaussian norm bound around the differentiation point. -/
theorem norm_iteratedDeriv_le_of_gaussian_center {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {M a : ℝ} (ha : 0 < a) (z : ℂ)
    (hbound : ∀ w, ‖f w‖ ≤ M * Real.exp (a * ‖w - z‖ ^ 2)) (n : ℕ) :
    ‖iteratedDeriv n f z‖ ≤
      n.factorial * (M * Real.exp (((n : ℝ) + 1) / 2)) /
        (Real.sqrt (((n : ℝ) + 1) / (2 * a))) ^ n := by
  let r : ℝ := Real.sqrt (((n : ℝ) + 1) / (2 * a))
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : a * r ^ 2 = ((n : ℝ) + 1) / 2 := by
    dsimp only [r]
    rw [Real.sq_sqrt (by positivity)]
    field_simp [ha.ne']
  apply norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf.diffContOnCl
  intro w hw
  have hw' : ‖w - z‖ = r := mem_sphere_iff_norm.mp hw
  simpa only [hw', hr2] using hbound w

end Complex
