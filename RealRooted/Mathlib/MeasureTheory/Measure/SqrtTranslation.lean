/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.MeasureTheory.Measure.SqrtSymmetrization
public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform
import RealRooted.Mathlib.MeasureTheory.Measure.AeratedSeries
import RealRooted.Mathlib.MeasureTheory.Measure.MomentTranslation
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtMoments
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtSupport

/-!
# Translating the symmetric square-root law

The moment series is the binomial transform of the aerated series. A measure
carried by `[0,L]` becomes nonnegative after shifting its symmetric square-root
law by `sqrt L`.
-/

public section

open PowerSeries

namespace MeasureTheory.Measure

/-- Exact formal moment series of the translated symmetric square-root law. -/
theorem mk_moments_map_add_sqrtSymmetrization {mu : Measure ℝ}
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu) (c : ℝ) :
    PowerSeries.mk (fun n => ∫ x : ℝ, x ^ n ∂mu.sqrtSymmetrization.map (fun y => y + c)) =
      binomialTransform c
        ((PowerSeries.mk (fun n => ∫ x : ℝ, x ^ n ∂mu)).subst (X ^ 2 : ℝ⟦X⟧)) := by
  have hseq : (fun k => ∫ x : ℝ, x ^ k ∂mu.sqrtSymmetrization) =
      aeratedMoment (fun k => ∫ x : ℝ, x ^ k ∂mu) :=
    funext fun k => Measure.integral_pow_sqrtSymmetrization hmu k
  rw [← mk_aeratedMoment, binomialTransform_mk]
  apply congrArg PowerSeries.mk
  funext n
  rw [integral_pow_map_add (Measure.integrable_pow_sqrtSymmetrization hmu hmom) c n, hseq]

/-- The shift by the support radius makes the lifted measure nonnegative. -/
theorem ae_nonneg_map_add_sqrtSymmetrization {mu : Measure ℝ} {L : ℝ}
    (hmu : ∀ᵐ x ∂mu, x ∈ Set.Icc 0 L) :
    ∀ᵐ x ∂mu.sqrtSymmetrization.map (fun y => y + Real.sqrt L), 0 ≤ x := by
  apply (ae_map_iff (by fun_prop) measurableSet_Ici).mpr
  filter_upwards [ae_abs_sqrtSymmetrization_le hmu] with y hy
  have hy' := (abs_le.mp hy).1
  linarith

end MeasureTheory.Measure
