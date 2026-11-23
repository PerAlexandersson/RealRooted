/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTrace
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.SameSignTypeI
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.NativeWeightedHeatHierarchy
import RealRooted.Mathlib.Analysis.Complex.ZeroHeatTraceScale

/-!
# The weighted native integral identities under Zhang's source hypotheses

Either common sign of the real Taylor coefficients is allowed. The shared
Type-I normalization changes neither the logarithmic derivative nor the
actual native divisor heat trace. The order-below-one hypothesis removes
the exponential factor rather than postulating a pure product.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace RealRooted

/-- Zhang's negative-zero and strict same-sign Taylor assumptions imply
both native weighted-heat and Laguerre integral identities. -/
theorem native_weighted_heatTrace_logDeriv_of_sameSign
    {f : ℂ → ℂ} {rho : ℝ} (hf : Differentiable ℂ f)
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hzeros : ∀ z, f z = 0 → z.im = 0 ∧ z.re < 0)
    (hsign : ∀ n : ℕ, 0 < (f 0).re *
      ((iteratedDeriv n f 0).re / (n.factorial : ℝ)))
    (k m : ℕ) {x : ℝ} (hx : 0 < x) :
    (IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * (-t) ^ k *
        iteratedDeriv k (Complex.zeroHeatTrace f) t) (Ioi 0) ∧
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x =
          ∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m * (-t) ^ k *
            iteratedDeriv k (Complex.zeroHeatTrace f) t) ∧
    (IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ m * Complex.zeroHeatTrace f t *
        (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) (Ioi 0) ∧
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x =
          ∫ t : ℝ in Ioi 0, Real.exp (-x * t) * t ^ m * Complex.zeroHeatTrace f t *
            (Polynomial.generalizedLaguerre k (m : ℝ)).eval (-x * t)) := by
  obtain ⟨h0, c, hc, htype⟩ := exists_real_const_mul_isLaguerrePolyaTypeI_of_sameSign
    hf (horder.mono hrho.le) hconj (fun z hz ↦ (hzeros z hz).1) hsign
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hn0 : (fun z : ℂ ↦ (c : ℂ) * f z) 0 ≠ 0 := mul_ne_zero hcc h0
  have h := htype.native_weighted_heatTrace_logDeriv hn0 (horder.const_mul (c : ℂ)) hrho k m hx
  have hlog : logDeriv (fun z : ℂ ↦ (c : ℂ) * f z) = logDeriv f :=
    funext fun z ↦ logDeriv_const_mul z (c : ℂ) hcc
  simpa only [hlog, Complex.zeroHeatTrace_const_mul hcc] using h

end RealRooted
