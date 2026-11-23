/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.SameSignLogDerivativeHierarchy
import RealRooted.Mathlib.Analysis.Complex.RealSeries
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Zhang's same-sign series hypotheses

The actual real coefficient expansion from equation (1.1), together with
entirety, order below one and negative zeros, implies the two-index
complete-monotonicity conclusion. Conjugation symmetry and canonical
Taylor coefficients are derived from the supplied series rather than
being extra assumptions. A germ at zero suffices for an entire function.
-/

public section

open Filter Topology

namespace RealRooted

/-- The real-series formulation of Zhang's Theorem 1, including either
common coefficient sign and all nonnegative hierarchy indices. -/
theorem isCompletelyMonotoneOnIoi_weighted_logDeriv_of_series
    {f : ℂ → ℂ} {a : ℕ → ℝ} {rho : ℝ} (hf : Differentiable ℂ f)
    (hseries : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ (a n : ℂ) * z ^ n) (f z))
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hzeros : ∀ z : ℂ, f z = 0 → z.im = 0 ∧ z.re < 0)
    (hsign : ∀ n : ℕ, 0 < a 0 * a n) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦ y ^ (k + m) *
        iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x) := by
  have hc (n : ℕ) : (iteratedDeriv n f 0).re / (n.factorial : ℝ) = a n := by
    have h := congrArg Complex.re
      (Complex.iteratedDeriv_div_factorial_eq_of_hasSum (hf.analyticAt 0) hseries n)
    simpa only [Complex.div_natCast_re, Complex.ofReal_re] using h
  have hc0 : (f 0).re = a 0 := by
    simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] using hc 0
  apply isCompletelyMonotoneOnIoi_weighted_logDeriv_of_negZeros hf horder hrho
    (Complex.conj_of_real_hasSum_germ hf hseries) hzeros
  intro n
  rw [hc0, hc n]
  exact hsign n

end RealRooted
