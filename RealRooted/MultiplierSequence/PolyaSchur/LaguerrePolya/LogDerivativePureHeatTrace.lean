/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIPureProduct
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.PositiveSlopeHeatTrace
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHeatTrace

/-!
# Pure heat-trace representations below order one

Growth below order one removes the Type-I exponential constant, so every
signed logarithmic derivative is a heat-trace Laplace moment, including at
zero. This recovers the pure heat representation in Zhang's Lemma 2 from
the Type-I structural hypothesis and the growth estimate.
-/

public section

open MeasureTheory

namespace RealRooted

/-- The logarithmic derivative of a Type-I function of order below one
has a pure heat-trace representation, with no residual exponential term. -/
theorem IsLaguerrePolyaTypeI.exists_pure_heatTrace_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) :
    ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ Summable a ∧
      f = (fun z : ℂ ↦ f 0 * ∏' i, (1 + (a i : ℂ) * z)) ∧
      TauCeti.IsCompletelyMonotoneOnIoi (Real.positiveSlopeHeatTrace a) ∧
      ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Real.positiveSlopeHeatTrace a t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦ (logDeriv f (y : ℂ)).re) x =
          ∫ t : ℝ in Set.Ioi 0,
            Real.exp (-x * t) * t ^ k * Real.positiveSlopeHeatTrace a t := by
  obtain ⟨a, ha, hs, heq⟩ := hf.exists_eq_prod_of_order_lt_one h0 horder hrho
  refine ⟨a, ha, hs, heq, Real.isCompletelyMonotoneOnIoi_positiveSlopeHeatTrace hs,
    fun k x hx ↦ ⟨(Real.laplace_positiveSlopeHeatTrace ha hs k hx).1, ?_⟩⟩
  have h := signed_iteratedDeriv_re_logDeriv_exp_linear_product h0 0 ha hs k hx
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, zero_add] at h
  simpa only [← heq] using h

end RealRooted
