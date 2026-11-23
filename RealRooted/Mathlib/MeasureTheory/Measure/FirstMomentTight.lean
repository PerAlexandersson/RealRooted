/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight

/-!
# Tightness from a bounded first moment on the nonnegative half-line

A family of positive measures with a common finite first-moment bound is
tight. Markov's inequality controls the mass outside a compact interval.
This statement does not require a positive total mass or normalization.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory

/-- A bounded first moment makes a family of measures on the nonnegative
half-line tight, including families containing the zero measure. -/
theorem isTightMeasureSet_of_lintegral_id_le {S : Set (Measure ℝ≥0)} {C : ℝ≥0}
    (hC : ∀ μ ∈ S, ∫⁻ x : ℝ≥0, (x : ℝ≥0∞) ∂μ ≤ C) :
    IsTightMeasureSet S := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hδpos : 0 < δ := by exact_mod_cast hδ
  let R : ℝ≥0 := C / δ + 1
  have hR : 0 < R := by positivity
  have hquot : C / R ≤ δ := by
    rw [div_le_iff₀ hR]
    calc
      C = δ * (C / δ) := by rw [mul_comm δ, div_mul_cancel₀ _ hδpos.ne']
      _ ≤ δ * R := by
        gcongr
        exact le_add_of_nonneg_right zero_le_one
  refine ⟨Icc (0 : ℝ≥0) R, isCompact_Icc, fun μ hμ => ?_⟩
  calc
    μ (Icc (0 : ℝ≥0) R)ᶜ ≤ μ {x : ℝ≥0 | (R : ℝ≥0∞) ≤ (x : ℝ≥0∞)} := by
      apply measure_mono
      intro x hx
      have hx' : R < x := by simpa using hx
      exact ENNReal.coe_le_coe.mpr hx'.le
    _ ≤ (∫⁻ x : ℝ≥0, (x : ℝ≥0∞) ∂μ) / (R : ℝ≥0∞) :=
      meas_ge_le_lintegral_div (by fun_prop) (by exact_mod_cast hR.ne')
        ENNReal.coe_ne_top
    _ ≤ (C : ℝ≥0∞) / (R : ℝ≥0∞) := by gcongr; exact hC μ hμ
    _ ≤ (δ : ℝ≥0∞) := by
      rw [← ENNReal.coe_div hR.ne']
      exact ENNReal.coe_le_coe.mpr hquot
    _ ≤ ε := hδε.le

end MeasureTheory
