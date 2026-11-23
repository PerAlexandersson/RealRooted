/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Transporting atomic decompositions from nonnegative reals

A real measure carried by the nonnegative half-line is recovered by transport
to `ℝ≥0` followed by coercion back to `ℝ`. Atomic decompositions are preserved.
-/

public section

open scoped NNReal ENNReal

namespace MeasureTheory.Measure

/-- Transport to nonnegative reals followed by coercion recovers a measure
carried by the nonnegative half-line. -/
theorem map_coe_map_toNNReal_of_ae_nonneg {mu : Measure ℝ}
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x) :
    (mu.map Real.toNNReal).map ((↑) : ℝ≥0 → ℝ) = mu := by
  rw [map_map measurable_coe_nnreal_real measurable_real_toNNReal]
  calc
    mu.map (((↑) : ℝ≥0 → ℝ) ∘ Real.toNNReal) = mu.map id := by
      apply map_congr
      filter_upwards [hpos] with x hx
      exact Real.coe_toNNReal x hx
    _ = mu := map_id

/-- An exact atomic decomposition after transport to `ℝ≥0` yields the same
decomposition on the real line, with unchanged masses. -/
theorem eq_atomic_of_map_toNNReal_eq {ι : Type*} {mu : Measure ℝ}
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x) {sigma : ℝ≥0∞} {w : ι → ℝ≥0∞} {a : ι → ℝ≥0}
    (hmu : mu.map Real.toNNReal = sigma • dirac 0 +
      Measure.sum (fun i ↦ w i • dirac (a i))) :
    mu = sigma • dirac 0 + Measure.sum (fun i ↦ w i • dirac (a i : ℝ)) := by
  calc
    mu = (mu.map Real.toNNReal).map ((↑) : ℝ≥0 → ℝ) :=
      (map_coe_map_toNNReal_of_ae_nonneg hpos).symm
    _ = _ := by
      rw [hmu, Measure.map_add _ _ measurable_coe_nnreal_real,
        Measure.map_sum measurable_coe_nnreal_real.aemeasurable]
      simp only [Measure.map_smul _ measurable_coe_nnreal_real.aemeasurable,
        Measure.map_dirac' measurable_coe_nnreal_real, NNReal.coe_zero]

end MeasureTheory.Measure
