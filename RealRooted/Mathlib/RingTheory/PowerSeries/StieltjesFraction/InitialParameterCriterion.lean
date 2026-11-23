/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportParameters

import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportCriterion
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerParameters

/-!
# The lower-support criterion with arbitrary initial parameter

This is Sokal-Walrad, arXiv:2404.12131v1, Theorem 2(a)-(c).
The initial even parameter may be any nonnegative real number.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- A lower-support parametrization can have an arbitrary nonnegative
initial parameter instead of the normalization `u 0 = 0`. -/
theorem exists_measure_moments_Ici_iff_nonneg_parameters
    (m : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    ∃ (a : ℝ) (u v : ℕ → ℝ), 0 ≤ a ∧
      (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧
      mk m = C a * stieltjesTail (shiftedStieltjesNumerators c u v) 0 := by
  rw [exists_measure_moments_Ici_iff_parameters _ hc]
  constructor
  · rintro ⟨a, u, v, ha, _, hu, hv, hf⟩
    exact ⟨a, u, v, ha, hu, hv, hf⟩
  · rintro ⟨a, u, v, ha, hu, hv, hf⟩
    obtain ⟨u', v', hu0, hu', hv', heq⟩ :=
      exists_lower_stieltjesParameters hc hu hv (r := 0) le_rfl (hu 0)
    refine ⟨a, u', v', ha, hu0, fun k => (hu' k).1, fun k => (hv k).trans (hv' k), ?_⟩
    simpa only [heq] using hf

end PowerSeries
