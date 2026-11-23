/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.PowerSum
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeILinearProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.PowerSumMoments
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Star
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star


/-!
# The exact logarithmic moment measure of a positive linear product
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- The slope-weighted atomic measure is the actual complex logarithmic moment
measure of a summable positive linear product. Zero slopes contribute zero mass. -/
theorem logDeriv_tprod_moments_sum_smul_dirac {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k)
      (Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i))) ∧
    (-1 : ℂ) ^ k * iteratedDeriv k
      (logDeriv (fun z : ℂ => ∏' i, (1 + (a i : ℂ) * z))) 0 / k.factorial =
      ((∫ x : ℝ, x ^ k ∂Measure.sum
        (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)) : ℝ) : ℂ) := by
  refine ⟨integrable_pow_sum_smul_dirac ha hs k, ?_⟩
  have hf := isLaguerrePolyaTypeI_tprod_one_add_mul ha hs
  have hreal := ofReal_re_iteratedDeriv_zero
    (logDeriv_conj (f := fun z : ℂ => ∏' i, (1 + (a i : ℂ) * z))
      hf.toLaguerrePolya.conj) k
  have h := congrArg (fun t : ℝ => (t : ℂ))
    ((signed_logDeriv_linear_product a hs k).trans
      (integral_pow_sum_smul_dirac ha k).symm)
  simpa only [ofReal_div, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one,
    ofReal_natCast, hreal] using h

end RealRooted
