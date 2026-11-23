/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIPureProduct
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHeatTrace

/-!
# Intrinsic zero heat traces of Type-I functions below order one

These statements use the actual native divisor, with all zero multiplicities.
The growth hypothesis removes the exponential correction. The Laplace
moments recover every signed logarithmic derivative as in Zhang's Lemma 2,
including at zero, without choosing an enumeration in the statement.
-/

public section

open Complex Filter MeasureTheory Topology

namespace RealRooted

/-- The native zero heat trace is completely monotone and its Laplace
moments are all signed logarithmic derivatives, including at zero. -/
theorem IsLaguerrePolyaTypeI.native_heatTrace_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) :
    TauCeti.IsCompletelyMonotoneOnIoi (Complex.zeroHeatTrace f) ∧
      ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Complex.zeroHeatTrace f t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦ (logDeriv f (y : ℂ)).re) x =
          ∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k * Complex.zeroHeatTrace f t := by
  obtain ⟨a, ha, hs, heq⟩ := hf.exists_eq_prod_of_order_lt_one h0 horder hrho
  have hcm := Complex.isCompletelyMonotoneOnIoi_zeroHeatTrace_linearProduct h0 ha hs
  refine ⟨by simpa only [← heq] using hcm, fun k x hx ↦ ?_⟩
  have hnative := Complex.laplace_zeroHeatTrace_linearProduct h0 ha hs k hx
  rw [← heq] at hnative
  refine ⟨hnative.1, ?_⟩
  have hreal := signed_iteratedDeriv_re_logDeriv_exp_linear_product h0 0 ha hs k hx
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, zero_add] at hreal
  rw [← heq] at hreal
  exact hreal.trans ((Real.laplace_positiveSlopeHeatTrace ha hs k hx).2.trans hnative.2.symm)

end RealRooted
