/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.MeasureTheory.Measure.SqrtSymmetrization

/-!
# Support of the symmetric square-root law

Support in the closed interval `[0,L]` becomes support in
`[-sqrt L,sqrt L]`. The converse follows by squaring. The zero measure, origin
atoms, and `L=0` are included; no moments or finite-mass hypothesis is required.
-/

public section

namespace MeasureTheory.Measure

/-- Closed-interval support gives the corresponding symmetric square-root bound. -/
theorem ae_abs_sqrtSymmetrization_le {mu : Measure ℝ} {L : ℝ}
    (hmu : ∀ᵐ x ∂mu, x ∈ Set.Icc 0 L) :
    ∀ᵐ x ∂mu.sqrtSymmetrization, |x| ≤ Real.sqrt L := by
  apply ae_smul_measure
  apply ae_add_measure_iff.mpr
  constructor
  · apply (ae_map_iff (by fun_prop)
      (isClosed_le continuous_abs continuous_const).measurableSet).mpr
    filter_upwards [hmu] with x hx
    simpa only [abs_of_nonneg (Real.sqrt_nonneg x)] using Real.sqrt_le_sqrt hx.2
  · apply (ae_map_iff (by fun_prop)
      (isClosed_le continuous_abs continuous_const).measurableSet).mpr
    filter_upwards [hmu] with x hx
    simpa only [abs_neg, abs_of_nonneg (Real.sqrt_nonneg x)] using Real.sqrt_le_sqrt hx.2

/-- Squaring a supported symmetric lift recovers the original upper bound. -/
theorem ae_mem_Icc_of_sqrtSymmetrization {mu : Measure ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hs : ∀ᵐ x ∂mu.sqrtSymmetrization, |x| ≤ Real.sqrt L) :
    ∀ᵐ x ∂mu, x ∈ Set.Icc 0 L := by
  rw [← map_sq_sqrtSymmetrization hmu]
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
  filter_upwards [hs] with x hx
  refine ⟨sq_nonneg x, ?_⟩
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 2
  simpa only [sq_abs, Real.sq_sqrt hL] using hp

/-- The exact support equivalence for a nonnegative measure. -/
theorem ae_mem_Icc_iff_sqrtSymmetrization {mu : Measure ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x) :
    (∀ᵐ x ∂mu, x ∈ Set.Icc 0 L) ↔
      ∀ᵐ x ∂mu.sqrtSymmetrization, x ∈ Set.Icc (-Real.sqrt L) (Real.sqrt L) := by
  simpa only [Set.mem_Icc, ← abs_le] using
    (show (∀ᵐ x ∂mu, x ∈ Set.Icc 0 L) ↔
        ∀ᵐ x ∂mu.sqrtSymmetrization, |x| ≤ Real.sqrt L from
      ⟨ae_abs_sqrtSymmetrization_le, ae_mem_Icc_of_sqrtSymmetrization hL hmu⟩)

end MeasureTheory.Measure
