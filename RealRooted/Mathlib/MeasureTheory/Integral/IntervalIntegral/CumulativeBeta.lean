/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.CumulativeDerivative
import RealRooted.Mathlib.Analysis.SpecialFunctions.Gamma.BetaVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith

/-!
# Beta-weighted error from finite cumulative discrepancy

For nonnegative exponents, the integration error against `t^a (1-t)^b` is at
most twice the cumulative discrepancy. The weights may be signed, and nodes
at both endpoints are included. This quantitative result uses an integrable
interior derivative, not a continuous derivative at the endpoints.
-/

public section

namespace Finset

variable {ι : Type*}

/-- Finite cumulative discrepancy bounds every beta-weighted sum with nonnegative exponents.
The constant two is uniform in both exponents. Signed weights and repeated nodes are allowed. -/
theorem abs_sum_beta_weight_sub_le_of_cumulative_bound (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |(∑ i ∈ s, w i * (r i ^ a * (1 - r i) ^ b)) -
        ∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ b| ≤ 2 * δ := by
  obtain ⟨g, hg, hderiv, hvariation⟩ :=
    Real.exists_integrable_deriv_rpow_mul_one_sub_rpow ha hb
  have hcont : Continuous (fun t : ℝ ↦ t ^ a * (1 - t) ^ b) :=
    (Real.continuous_rpow_const ha).mul
      ((Real.continuous_rpow_const hb).comp (continuous_const.sub continuous_id))
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 1 ⟨zero_le_one, le_rfl⟩)
  calc
    _ ≤ δ * (|(1 : ℝ) ^ a * (1 - 1) ^ b| + ∫ t in (0 : ℝ)..1, |g t|) :=
      abs_sum_mul_sub_integral_le_of_cumulative_bound s r w hr hδ hcont.continuousOn hderiv hg
    _ ≤ δ * 2 := mul_le_mul_of_nonneg_left hvariation hδ0
    _ = 2 * δ := mul_comm _ _

end Finset
