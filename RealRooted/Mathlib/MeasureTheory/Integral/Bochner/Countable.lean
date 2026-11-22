/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integrals on countable sets as convergent atomic sums

These strengthen the countable-integral formulas to `HasSum`, so summability of
the atomic series is retained in subsequent arguments.
-/

public section

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} {f : X → E}

/-- The integral on a countable space is the sum of the weighted values at its
atoms, with convergence included. -/
theorem hasSum_integral_countable [Countable X] (hf : Integrable f μ) :
    HasSum (fun x => μ.real {x} • f x) (∫ x, f x ∂μ) := by
  have hf' : Integrable f (Measure.sum fun x => μ {x} • Measure.dirac x) := by
    rwa [Measure.sum_smul_dirac]
  simpa only [integral_smul_measure, integral_dirac, Measure.sum_smul_dirac,
    measureReal_def] using hasSum_integral_measure hf'

/-- An integral over a countable set is the convergent sum over its atoms. -/
theorem hasSum_setIntegral_countable (f : X → E) {s : Set X} (hs : s.Countable)
    (hf : IntegrableOn f s μ) :
    HasSum (fun x : s => μ.real {(x : X)} • f x) (∫ x in s, f x ∂μ) := by
  have hi : Countable s := Set.countable_coe_iff.mpr hs
  have hf' : Integrable (fun x : s => f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn, ← map_comap_subtype_coe, integrable_map_measure] at hf
    · exact hf
    · exact hf.aestronglyMeasurable
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact hs.measurableSet
  convert hasSum_integral_countable hf' using 1
  · ext x
    rw [measureReal_def, measureReal_def, Measure.comap_apply Subtype.val
      Subtype.coe_injective (fun t ht => MeasurableSet.subtype_image hs.measurableSet ht)
      _ (MeasurableSet.singleton x)]
    simp
  · exact (integral_subtype_comap hs.measurableSet f).symm

/-- A measure carried by a countable set integrates by a convergent sum of its
atomic weights times the values of the integrand. -/
theorem hasSum_integral_of_ae_mem_countable {s : Set X} (hs : s.Countable)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hf : Integrable f μ) :
    HasSum (fun x : s => μ.real {(x : X)} • f x) (∫ x, f x ∂μ) := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
    hasSum_setIntegral_countable f hs hf.integrableOn

end MeasureTheory
