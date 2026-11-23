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
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.SameSignNativeWeightedHeat
import RealRooted.Mathlib.Analysis.Complex.RealSeries
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The supplied-real-series form of Zhang's weighted heat identities

The genuine real coefficient series, entirety, order below one, negative
zeros and strict common coefficient sign give both weighted native integrals.
Canonical Taylor coefficients and conjugation symmetry are derived from
the supplied germ, so they are not additional assumptions.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace RealRooted

/-- The exact supplied-real-series hypotheses yield both native integral
representations, for either coefficient sign and every hierarchy index. -/
theorem native_weighted_heatTrace_logDeriv_of_series
    {f : ℂ → ℂ} {a : ℕ → ℝ} {rho : ℝ} (hf : Differentiable ℂ f)
    (hseries : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ (a n : ℂ) * z ^ n) (f z))
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hzeros : ∀ z : ℂ, f z = 0 → z.im = 0 ∧ z.re < 0)
    (hsign : ∀ n : ℕ, 0 < a 0 * a n)
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
  have hc := Complex.re_iteratedDeriv_div_factorial_eq_of_hasSum (hf.analyticAt 0) hseries
  have hc0 : (f 0).re = a 0 := by
    simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] using hc 0
  have hsign' : ∀ n : ℕ, 0 < (f 0).re *
      ((iteratedDeriv n f 0).re / (n.factorial : ℝ)) := by
    intro n
    rw [hc0, hc n]
    exact hsign n
  exact native_weighted_heatTrace_logDeriv_of_sameSign hf horder hrho
    (Complex.conj_of_real_hasSum_germ hf hseries) hzeros hsign' k m hx

end RealRooted
