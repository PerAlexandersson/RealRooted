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
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeHierarchy
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.SameSignTypeI

/-!
# Same-sign Taylor data and the logarithmic-derivative hierarchy

Zhang's Theorem 1 assumes a real entire function of order below one,
negative zeros, and `a₀ aₙ > 0` for its Taylor coefficients. The coefficient
condition is written here using the actual derivatives divided by `n!`.
Multiplying by the nonzero real value at zero normalizes the sign and
leaves all logarithmic derivatives unchanged. The argument works more
generally at order at most one when all zeros are real.
-/

public section

open scoped ComplexConjugate

namespace RealRooted

/-- Same-sign Taylor coefficients normalize a real entire function with
real zeros to Type-I, giving the complete signed derivative hierarchy. -/
theorem isCompletelyMonotoneOnIoi_weighted_logDeriv_of_sameSign
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f 1)
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hzeros : ∀ z, f z = 0 → z.im = 0)
    (hsign : ∀ n : ℕ, 0 < (f 0).re *
      ((iteratedDeriv n f 0).re / (n.factorial : ℝ))) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
        y ^ (k + m) * iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x) := by
  obtain ⟨h0, c, hc, htype⟩ := exists_real_const_mul_isLaguerrePolyaTypeI_of_sameSign
    hf horder hconj hzeros hsign
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hn0 : (fun z : ℂ ↦ (c : ℂ) * f z) 0 ≠ 0 := mul_ne_zero hcc h0
  have hlog : logDeriv (fun z : ℂ ↦ (c : ℂ) * f z) = logDeriv f :=
    funext fun z ↦ logDeriv_const_mul z (c : ℂ) hcc
  simpa only [hlog] using htype.isCompletelyMonotoneOnIoi_weighted_logDeriv hn0 k m

/-- Zhang's strict order-below-one and negative-zero hypotheses imply
the actual two-index derivative family from his Theorem 1. -/
theorem isCompletelyMonotoneOnIoi_weighted_logDeriv_of_negZeros
    {f : ℂ → ℂ} {rho : ℝ} (hf : Differentiable ℂ f)
    (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hzeros : ∀ z, f z = 0 → z.im = 0 ∧ z.re < 0)
    (hsign : ∀ n : ℕ, 0 < (f 0).re *
      ((iteratedDeriv n f 0).re / (n.factorial : ℝ))) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
        y ^ (k + m) * iteratedDeriv m (fun z : ℝ ↦ (logDeriv f (z : ℂ)).re) y) x) :=
  isCompletelyMonotoneOnIoi_weighted_logDeriv_of_sameSign hf (horder.mono hrho.le)
    hconj (fun z hz ↦ (hzeros z hz).1) hsign k m

end RealRooted
