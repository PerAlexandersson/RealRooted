/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Holomorphic
public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Inversion
import RealRooted.Mathlib.MeasureTheory.Measure.FiniteMomentStieltjes

/-!
# Nonnegative real moment measures and Stieltjes transforms

Transport a finite measure carried by `[0,∞)` to `ℝ≥0`, then apply the explicit
reciprocal-measure construction. This supplies genuine integrability and a
holomorphic transform on the slit plane, with no compact-support requirement.
-/

public section

open Complex MeasureTheory Set NNReal

namespace MeasureTheory.Measure

/-- Transport to `ℝ≥0` preserves the zero atom of a measure carried by `[0,∞)`. -/
theorem map_toNNReal_singleton_zero_of_ae_nonneg
    {mu : Measure ℝ} (hpos : ∀ᵐ x ∂mu, 0 ≤ x) :
    mu.map Real.toNNReal {0} = mu {0} := by
  rw [map_apply measurable_real_toNNReal (measurableSet_singleton 0)]
  apply measure_congr
  filter_upwards [hpos] with x hx
  change (Real.toNNReal x = 0) ↔ (x = 0)
  rw [Real.toNNReal_eq_zero]
  exact ⟨fun h ↦ le_antisymm h hx, fun h ↦ h.le⟩

/-- The reciprocal-kernel integral is preserved when a nonnegative real measure
is transported to `ℝ≥0`. This is an identity of complex integrals. -/
theorem integral_inv_one_add_mul_map_toNNReal
    {mu : Measure ℝ} (hpos : ∀ᵐ x ∂mu, 0 ≤ x) (z : ℂ) :
    (∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu.map Real.toNNReal) =
      ∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu := by
  rw [integral_map_of_stronglyMeasurable measurable_real_toNNReal (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  rw [Real.coe_toNNReal x hx]

/-- The moment kernel of a finite nonnegative real measure is integrable at
each point of the slit plane. -/
theorem integrable_inv_one_add_mul_of_ae_nonneg
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    {z : ℂ} (hz : z ∈ slitPlane) :
    Integrable (fun x : ℝ ↦ (1 + z * (x : ℂ))⁻¹) mu := by
  have hi := (mu.map Real.toNNReal).integrable_inv_one_add_mul_of_mem_slitPlane hz
  apply (hi.comp_measurable measurable_real_toNNReal).congr
  filter_upwards [hpos] with x hx
  simp only [Function.comp_apply, Real.coe_toNNReal x hx]

/-- The moment transform has explicit Stieltjes data. The original zero atom is
the constant coefficient, and the reciprocal measure can have infinite mass. -/
theorem integral_inv_one_add_mul_eq_stieltjesExtension_of_ae_nonneg
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu) =
      TauCeti.stieltjesExtension (mu.map Real.toNNReal).stieltjesInversion 0
        (Real.toNNReal (mu.real {0})) z := by
  rw [← integral_inv_one_add_mul_map_toNNReal hpos z,
    (mu.map Real.toNNReal).integral_inv_one_add_mul_eq_stieltjesExtension hz]
  have hatom : (mu.map Real.toNNReal).real {0} = mu.real {0} :=
    congrArg ENNReal.toReal (map_toNNReal_singleton_zero_of_ae_nonneg hpos)
  simp only [hatom]

/-- The complex reciprocal transform of a finite measure on `[0,∞)` is
holomorphic on the slit plane. -/
theorem analyticOnNhd_integral_inv_one_add_mul_of_ae_nonneg
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hpos : ∀ᵐ x ∂mu, 0 ≤ x) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ x : ℝ, (1 + z * (x : ℂ))⁻¹ ∂mu) slitPlane := by
  apply (TauCeti.analyticOnNhd_stieltjesExtension
    (μ := (mu.map Real.toNNReal).stieltjesInversion)
    (a := 0) (b := (Real.toNNReal (mu.real {0})))).congr isOpen_slitPlane
  intro z hz
  exact (integral_inv_one_add_mul_eq_stieltjesExtension_of_ae_nonneg hpos hz).symm

/-- The actual real part of the complex transform has the explicit reciprocal
Stieltjes representation, including the original zero atom. -/
theorem representsStieltjes_integral_inv_one_add_mul_of_ae_nonneg
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hpos : ∀ᵐ x ∂mu, 0 ≤ x) :
    TauCeti.RepresentsStieltjes (mu.map Real.toNNReal).stieltjesInversion 0
      (Real.toNNReal (mu.real {0}))
      (fun t : ℝ ↦ (∫ x : ℝ, (1 + (t : ℂ) * (x : ℂ))⁻¹ ∂mu).re) := by
  have hs := (mu.map Real.toNNReal).representsStieltjes_integral_inv_one_add_mul
  have hatom : (mu.map Real.toNNReal).real {0} = mu.real {0} :=
    congrArg ENNReal.toReal (map_toNNReal_singleton_zero_of_ae_nonneg hpos)
  rw [hatom] at hs
  apply hs.congr
  intro t _
  exact congrArg Complex.re (integral_inv_one_add_mul_map_toNNReal hpos t).symm

/-- A finite nonnegative moment transform is a Stieltjes function. -/
theorem isStieltjesFunction_integral_inv_one_add_mul_of_ae_nonneg
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hpos : ∀ᵐ x ∂mu, 0 ≤ x) :
    TauCeti.IsStieltjesFunction
      (fun t : ℝ ↦ (∫ x : ℝ, (1 + (t : ℂ) * (x : ℂ))⁻¹ ∂mu).re) := by
  apply TauCeti.isStieltjesFunction_iff.mpr
  exact ⟨0, (Real.toNNReal (mu.real {0})),
    (mu.map Real.toNNReal).stieltjesInversion,
    representsStieltjes_integral_inv_one_add_mul_of_ae_nonneg hpos⟩

end MeasureTheory.Measure

end
