/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Complex.Pick.Nevanlinna
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite Nevanlinna data associated with nonnegative moments

Weight a measure on `ℝ≥0` by `x / (1+x²)` and push it forward by `x ↦ -1/x`.
The weight is bounded, so finite moment measures yield finite Nevanlinna
measures. The zero atom disappears from this measure and contributes only to
the real constant in the representation of the negative moment transform.
-/

public section

open Complex MeasureTheory Set
open scoped NNReal ENNReal

namespace MeasureTheory.Measure

/-- The bounded density converting a moment transform to Nevanlinna form. -/
@[expose] noncomputable def momentNevanlinnaWeight (x : ℝ≥0) : ℝ≥0 :=
  x / (1 + x ^ 2)

/-- The real value of the moment-to-Nevanlinna density. -/
theorem coe_momentNevanlinnaWeight (x : ℝ≥0) :
    (momentNevanlinnaWeight x : ℝ) = (x : ℝ) / (1 + (x : ℝ) ^ 2) := by
  simp only [momentNevanlinnaWeight, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_one, NNReal.coe_pow]

/-- The moment-to-Nevanlinna density is measurable. -/
@[fun_prop]
theorem measurable_momentNevanlinnaWeight : Measurable momentNevanlinnaWeight := by
  unfold momentNevanlinnaWeight
  fun_prop

/-- The conversion density is at most one, including at zero. -/
theorem momentNevanlinnaWeight_le_one (x : ℝ≥0) : momentNevanlinnaWeight x ≤ 1 := by
  change x / (1 + x ^ 2) ≤ 1
  apply (div_le_one (by positivity : 0 < 1 + x ^ 2)).mpr
  have hx : (x : ℝ) ≤ 1 + (x : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((x : ℝ) - 1), x.coe_nonneg]
  exact_mod_cast hx

/-- A finite measure on nonnegative slopes induces a measure on negative roots. -/
@[expose] noncomputable def momentNevanlinna (mu : Measure ℝ≥0) : Measure ℝ :=
  (mu.withDensity fun x ↦ (momentNevanlinnaWeight x : ℝ≥0∞)).map
    (fun x : ℝ≥0 ↦ -(x : ℝ)⁻¹)

/-- Finiteness of the original moment measure suffices for finite Nevanlinna
data; no inverse moment or bounded-away-from-zero support is required. -/
theorem isFiniteMeasure_momentNevanlinna
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu] : IsFiniteMeasure mu.momentNevanlinna := by
  have hw : Integrable (fun x : ℝ≥0 ↦ (momentNevanlinnaWeight x : ℝ)) mu := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (momentNevanlinnaWeight x).coe_nonneg]
    exact_mod_cast momentNevanlinnaWeight_le_one x
  have : IsFiniteMeasure (mu.withDensity fun x ↦ (momentNevanlinnaWeight x : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      isFiniteMeasure_withDensity_ofReal hw.hasFiniteIntegral
  exact Measure.isFiniteMeasure_map _ _

/-- Integration against the moment-induced Nevanlinna measure is explicit. -/
theorem integral_momentNevanlinna
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure ℝ≥0) {g : ℝ → E} (hg : StronglyMeasurable g) :
    (∫ r : ℝ, g r ∂mu.momentNevanlinna) =
      ∫ x : ℝ≥0, (momentNevanlinnaWeight x : ℝ) • g (-(x : ℝ)⁻¹) ∂mu := by
  rw [momentNevanlinna, integral_map_of_stronglyMeasurable (by fun_prop) hg,
    integral_withDensity_eq_integral_smul (by fun_prop)]
  simp only [NNReal.smul_def]

/-- The negative reciprocal map is injective on `ℝ≥0`, with totalized inverse
sending zero to zero. -/
private theorem negative_reciprocal_injective :
    Function.Injective (fun x : ℝ≥0 ↦ -(x : ℝ)⁻¹) := by
  intro x y h
  exact NNReal.coe_injective (inv_injective (neg_injective h))

/-- The mass at a reciprocal root is the original atom times the conversion
density. The formula remains valid at zero, where the density is zero. -/
theorem momentNevanlinna_singleton (mu : Measure ℝ≥0) (a : ℝ≥0) :
    mu.momentNevanlinna {-(a : ℝ)⁻¹} =
      (momentNevanlinnaWeight a : ℝ≥0∞) * mu {a} := by
  rw [momentNevanlinna, map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : (fun x : ℝ≥0 ↦ -(x : ℝ)⁻¹) ⁻¹' {-(a : ℝ)⁻¹} = {a} := by
    ext x
    exact negative_reciprocal_injective.eq_iff
  rw [hpre, withDensity_apply _ (measurableSet_singleton _)]
  simp [mul_comm]

/-- The real singleton mass formula for the finite Nevanlinna measure. -/
theorem momentNevanlinna_real_singleton (mu : Measure ℝ≥0) (a : ℝ≥0) :
    mu.momentNevanlinna.real {-(a : ℝ)⁻¹} =
      (a : ℝ) / (1 + (a : ℝ) ^ 2) * mu.real {a} := by
  rw [measureReal_def, momentNevanlinna_singleton, ENNReal.toReal_mul,
    ENNReal.coe_toReal, coe_momentNevanlinnaWeight]
  rfl

/-- The moment-induced Nevanlinna measure has no atom at the origin. -/
theorem momentNevanlinna_singleton_zero (mu : Measure ℝ≥0) :
    mu.momentNevanlinna {0} = 0 := by
  simpa [momentNevanlinnaWeight] using mu.momentNevanlinna_singleton 0

end MeasureTheory.Measure

end
