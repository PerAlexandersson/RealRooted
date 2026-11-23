/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.MeasureTheory.Measure.MomentNevanlinna
public import TauCeti.Analysis.Complex.Pick.Nevanlinna

/-!
# Nevanlinna representation of a moment transform

The finite moment measure gives explicit Nevanlinna data with linear coefficient
zero. This identifies the representing measure before any canonical-product or
growth theorem is used.
-/

public section

open Complex MeasureTheory Set
open scoped NNReal ENNReal

namespace MeasureTheory.Measure

/-- The algebraic moment-to-Nevanlinna kernel identity, including slope zero. -/
private theorem neg_inv_one_add_mul_eq_nevanlinnaKernel {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) (x : ℝ≥0) :
    -(1 + z * ((x : ℝ) : ℂ))⁻¹ =
      ((momentNevanlinnaWeight x : ℝ) : ℂ) * TauCeti.nevanlinnaKernel z (-(x : ℝ)⁻¹) -
        (((1 + (x : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · simp [hx, momentNevanlinnaWeight]
  have hxC : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hx)
  have hd : -(((x : ℝ) : ℂ))⁻¹ - z ≠ 0 := by
    intro heq
    have hi := congrArg Complex.im heq
    have hxi : ((((x : ℝ) : ℂ))⁻¹).im = 0 := by
      rw [← Complex.ofReal_inv, Complex.ofReal_im]
    simp only [sub_im, neg_im, hxi, neg_zero, zero_sub, zero_im, neg_eq_zero] at hi
    exact (ne_of_gt hz) hi
  have hfac : 1 + z * ((x : ℝ) : ℂ) =
      -((x : ℝ) : ℂ) * (-(((x : ℝ) : ℂ))⁻¹ - z) := by
    calc
      _ = ((x : ℝ) : ℂ) * (((x : ℝ) : ℂ))⁻¹ + z * ((x : ℝ) : ℂ) := by
        rw [mul_inv_cancel₀ hxC]
      _ = _ := by ring
  have hd1 : 1 + z * ((x : ℝ) : ℂ) ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero (neg_ne_zero.mpr hxC) hd
  have hd2 : 1 + ((x : ℝ) : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show 1 + (x : ℝ) ^ 2 ≠ 0 by positivity)
  have hd3 : -1 - ((x : ℝ) : ℂ) * z ≠ 0 := by
    rw [show -1 - ((x : ℝ) : ℂ) * z = -(1 + z * ((x : ℝ) : ℂ)) by ring]
    exact neg_ne_zero.mpr hd1
  rw [coe_momentNevanlinnaWeight, TauCeti.nevanlinnaKernel_def]
  push_cast
  field_simp [hxC, hd, hd1, hd2]
  field_simp [hd3]
  ring

/-- The real correction kernel is integrable against every finite slope measure. -/
private theorem integrable_inv_one_add_sq
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] :
    Integrable (fun x : ℝ≥0 ↦ (1 + (x : ℝ) ^ 2)⁻¹) mu := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (x : ℝ)])

/-- Explicit finite Nevanlinna representation of the negative moment transform.
The linear coefficient is exactly zero; the correction constant is real. -/
theorem neg_integral_inv_one_add_mul_eq_nevanlinna
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    -(∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) =
      (∫ r : ℝ, TauCeti.nevanlinnaKernel z r ∂mu.momentNevanlinna) -
        ((∫ x : ℝ≥0, (1 + (x : ℝ) ^ 2)⁻¹ ∂mu : ℝ) : ℂ) := by
  have : IsFiniteMeasure mu.momentNevanlinna := mu.isFiniteMeasure_momentNevanlinna
  have hk := TauCeti.integrable_nevanlinnaKernel hz mu.momentNevanlinna
  change Integrable (TauCeti.nevanlinnaKernel z)
    ((mu.withDensity fun x ↦ (momentNevanlinnaWeight x : ℝ≥0∞)).map
      (fun x : ℝ≥0 ↦ -(x : ℝ)⁻¹)) at hk
  have hk' : Integrable (fun x : ℝ≥0 ↦ (momentNevanlinnaWeight x : ℝ) •
      TauCeti.nevanlinnaKernel z (-(x : ℝ)⁻¹)) mu :=
    (integrable_withDensity_iff_integrable_coe_smul
      measurable_momentNevanlinnaWeight).mp (hk.comp_measurable (by fun_prop))
  have hc : Integrable (fun x : ℝ≥0 ↦ (((1 + (x : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) mu :=
    (integrable_inv_one_add_sq mu).ofReal
  rw [mu.integral_momentNevanlinna (TauCeti.measurable_nevanlinnaKernel z).stronglyMeasurable]
  calc
    -(∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) =
        ∫ x : ℝ≥0, -(1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu := (integral_neg _).symm
    _ = ∫ x : ℝ≥0, (momentNevanlinnaWeight x : ℝ) •
        TauCeti.nevanlinnaKernel z (-(x : ℝ)⁻¹) -
          (((1 + (x : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) ∂mu := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
        simpa only [Complex.real_smul] using neg_inv_one_add_mul_eq_nevanlinnaKernel hz x)
    _ = _ := by
      simpa only [integral_complex_ofReal] using
        integral_sub hk' hc

end MeasureTheory.Measure

end
