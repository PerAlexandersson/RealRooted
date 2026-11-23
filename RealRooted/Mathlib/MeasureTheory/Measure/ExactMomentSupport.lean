/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import RealRooted.Mathlib.MeasureTheory.Measure.MomentDeterminacy

/-!
# The exact radius from geometric even-moment bounds
-/

public section

namespace MeasureTheory

/-- Geometric even-moment bounds confine a positive measure to the stated
closed radius, including radius zero. -/
theorem ae_abs_le_of_even_moment_bound {mu : Measure ℝ} {C R : ℝ} (hR : 0 ≤ R)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ (2 * n)) mu)
    (hbound : ∀ n : ℕ, (∫ x : ℝ, x ^ (2 * n) ∂mu) ≤ C * R ^ (2 * n)) :
    ∀ᵐ x ∂mu, |x| ≤ R := by
  apply (ae_le_const_iff_forall_gt_measure_zero (fun x : ℝ => |x|) R).mpr
  intro T hT
  exact measure_abs_ge_eq_zero_of_even_moment_bound hR hT hint hbound

end MeasureTheory
