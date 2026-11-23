/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
public import TauCeti.Analysis.Analytic.TaylorSeries
import RealRooted.Mathlib.Analysis.Analytic.TaylorSeries
import Mathlib.Tactic.TypeStar

/-!
# Real moment coefficients of the complex moment-generating Taylor series
-/

public section

open Complex MeasureTheory Set

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {Y : Ω → ℝ}

/-- At zero the complex MGF derivatives are the genuine real moments, embedded
in the complex numbers. Exponential integrability supplies all these moments. -/
theorem iteratedDeriv_complexMGF_zero
    (h0 : 0 ∈ interior (integrableExpSet Y mu)) (k : ℕ) :
    iteratedDeriv k (complexMGF Y mu) 0 = ((∫ w, Y w ^ k ∂mu : ℝ) : ℂ) := by
  rw [iteratedDeriv_complexMGF (by simpa only [zero_re] using h0)]
  simp only [zero_mul, exp_zero, mul_one, ← ofReal_pow]
  exact integral_complex_ofReal

/-- The complex MGF Taylor series is the coefficientwise real embedding of
the exponential moment series. This proves the required reality of all
coefficients without a separate conjugation hypothesis. -/
theorem taylorSeries_complexMGF_zero
    (h0 : 0 ∈ interior (integrableExpSet Y mu)) :
    TauCeti.taylorSeries (complexMGF Y mu) 0 =
      PowerSeries.map ofRealHom (PowerSeries.mk fun k =>
        (∫ w, Y w ^ k ∂mu) / k.factorial) := by
  ext k
  have hg : AnalyticAt ℂ (complexMGF Y mu) 0 :=
    analyticAt_complexMGF (by simpa only [zero_re] using h0)
  rw [hg.coeff_taylorSeries_eq_iteratedDeriv, iteratedDeriv_complexMGF_zero h0,
    PowerSeries.coeff_map, PowerSeries.coeff_mk]
  simp only [ofRealHom_eq_coe, ofReal_div, ofReal_natCast]

end ProbabilityTheory
