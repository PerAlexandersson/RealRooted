/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIOriginFactor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OriginLogDerivativeHierarchy
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OriginHeatTrace

/-!
# Logarithmic-derivative families for all nonzero Type-I functions

The native origin multiplicity is extracted by a checked analytic
factorization. Thus the caller supplies only Type-I membership and
nonzeroness of the function, not a chosen factorization or nonvanishing
at the origin. All parameter domains are the open positive half-line.
-/

public section

open MeasureTheory

namespace RealRooted

/-- The weighted logarithmic-derivative hierarchy of every nonzero
Type-I function is completely monotone, allowing zeros at the origin. -/
theorem IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_weighted_logDeriv_of_ne_zero
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (hfn : f ≠ 0) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x) := by
  obtain ⟨g, hg, hg0, heq⟩ := hf.exists_origin_factor hfn
  have h := hg.isCompletelyMonotoneOnIoi_weighted_logDeriv_pow_mul
    hg0 (analyticOrderNatAt f 0) k m
  simpa only [← heq] using h

/-- Every nonzero Type-I function below order one has its actual native
heat-trace Laplace representation at positive parameters, even with an origin zero. -/
theorem IsLaguerrePolyaTypeI.native_heatTrace_logDeriv_of_ne_zero
    {f : ℂ → ℂ} {rho : ℝ} (hf : IsLaguerrePolyaTypeI f) (hfn : f ≠ 0)
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) :
    TauCeti.IsCompletelyMonotoneOnIoi (Complex.zeroHeatTrace f) ∧
      ∀ (k : ℕ) (x : ℝ), 0 < x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Complex.zeroHeatTrace f t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦ (logDeriv f (y : ℂ)).re) x =
          ∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k * Complex.zeroHeatTrace f t := by
  obtain ⟨g, hg, hg0, hgorder, heq⟩ := hf.exists_origin_factor_of_order hfn horder hrho.le
  have h := hg.native_origin_heatTrace_logDeriv hg0 hgorder hrho (analyticOrderNatAt f 0)
  simpa only [← heq] using h

end RealRooted
