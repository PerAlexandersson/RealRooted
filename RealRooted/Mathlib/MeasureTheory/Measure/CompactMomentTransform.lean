/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The local transform of a bounded moment measure

For a finite measure supported in `[-R,R]`, its signed moments form the Taylor
series of `∫ (1 + z x)⁻¹`. A geometric majorant justifies integration term by
term. The statement also covers `R = 0` and the zero measure.
-/

public section

open Filter MeasureTheory Topology

namespace MeasureTheory.Measure

/-- A bounded moment measure has a locally convergent reciprocal-kernel series.
The bound is almost everywhere, so no topological support convention is needed. -/
theorem hasSum_moments_integral_inv {mu : Measure ℝ} [IsFiniteMeasure mu]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ x ∂mu, |x| ≤ R)
    {z : ℂ} (hz : ‖z‖ * R < 1) :
    HasSum (fun n : ℕ ↦ (-z) ^ n * ((∫ x : ℝ, x ^ n ∂mu : ℝ) : ℂ))
      (∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu) := by
  let q := ‖z‖ * R
  have hq : 0 ≤ q := mul_nonneg (norm_nonneg z) hR
  have hnorm (x : ℝ) (hx : |x| ≤ R) : ‖-z * (x : ℂ)‖ ≤ q := by
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg z)
  have hsum := hasSum_integral_of_dominated_convergence
    (μ := mu) (F := fun n : ℕ ↦ fun x : ℝ ↦ (-z * (x : ℂ)) ^ n)
    (f := fun x : ℝ ↦ (1 + z * (x : ℂ))⁻¹)
    (fun n _ ↦ q ^ n)
    (fun n ↦ ((continuous_const.mul Complex.continuous_ofReal).pow n).aestronglyMeasurable)
    (fun n ↦ hb.mono fun x hx ↦ by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm x hx) n)
    (Filter.Eventually.of_forall fun _ ↦ summable_geometric_of_lt_one hq hz)
    (integrable_const _)
    (hb.mono fun x hx ↦ by
      simpa only [neg_mul, sub_neg_eq_add] using
        hasSum_geometric_of_norm_lt_one ((hnorm x hx).trans_lt hz))
  simpa only [mul_pow, integral_const_mul, ← Complex.ofReal_pow, integral_complex_ofReal]
    using hsum

end MeasureTheory.Measure

end
