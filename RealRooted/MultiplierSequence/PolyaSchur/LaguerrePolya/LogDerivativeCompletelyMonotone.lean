/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIFactorization
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.Mathlib.Analysis.Complex.LinearProductLogDerivative
import RealRooted.Mathlib.Analysis.CompletelyMonotone.RationalMixtures
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.LogDeriv
import TauCeti.Analysis.CompletelyMonotone.OpenClosure

/-!
# Complete monotonicity of Type-I logarithmic derivatives

The logarithmic derivative of a Type-I function nonzero at zero is completely
monotone on the positive real axis. Its alternating real derivatives are
completely monotone as well. This gives the `k = 0` row of Ruiming Zhang,
*Complete monotonicity of special functions*, arXiv:1506.07012v13, Theorem 1.

The hypothesis is more general than the paper's order-below-one hypothesis:
nonnegative exponential factors, finite products and nonzero constants are
included. The `k > 0` weighted-derivative rows require a separate identity.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- The logarithmic derivative of a Type-I function is a nonnegative constant
plus the positive resolvent sum from its linear-product factorization, at
every nonnegative real argument. -/
theorem IsLaguerrePolyaTypeI.exists_re_logDeriv_eq_const_add_tsum
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    ∃ (gamma : ℝ) (a : ℕ → ℝ), 0 ≤ gamma ∧ (∀ i, 0 ≤ a i) ∧ Summable a ∧
      ∀ x : ℝ, 0 ≤ x → (logDeriv f (x : ℂ)).re =
        gamma + ∑' i, a i / (1 + a i * x) := by
  obtain ⟨gamma, a, hg, ha, hs, heq⟩ := hf.exists_eq_exp_mul_prod h0
  let P : ℂ → ℂ := fun z ↦ ∏' i, (1 + (a i : ℂ) * z)
  have hd : Differentiable ℂ P := Complex.differentiable_tprod_one_add_ofReal_mul hs
  refine ⟨gamma, a, hg, ha, hs, ?_⟩
  intro x hx
  have hP : P (x : ℂ) ≠ 0 := Complex.tprod_one_add_ofReal_mul_ne_zero ha hs hx
  have hlog : logDeriv f (x : ℂ) = (gamma : ℂ) + logDeriv P (x : ℂ) := by
    rw [heq]
    change logDeriv (fun z ↦ f 0 * exp ((gamma : ℂ) * z) * P z) (x : ℂ) = _
    rw [show (fun z ↦ f 0 * exp ((gamma : ℂ) * z) * P z) =
      (fun z ↦ f 0 * (exp ((gamma : ℂ) * z) * P z)) by funext z; ring]
    rw [logDeriv_const_mul _ _ h0,
      TauCeti.logDeriv_cexp_mul hP (hd (x : ℂ)) (by fun_prop), deriv_const_mul_id]
  rw [hlog, Complex.add_re, Complex.ofReal_re]
  exact congrArg (fun y : ℝ ↦ gamma + y) (Complex.re_logDeriv_tprod_one_add ha hs hx)

/-- A Type-I logarithmic derivative, restricted to the positive real axis,
is completely monotone. Smoothness is part of the conclusion. -/
theorem IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦ (logDeriv f (x : ℂ)).re) := by
  obtain ⟨gamma, a, hg, ha, hs, heq⟩ := hf.exists_re_logDeriv_eq_const_add_tsum h0
  have hc := (TauCeti.isCompletelyMonotone_const hg).isCompletelyMonotoneOnIoi
  have hm := TauCeti.isCompletelyMonotoneOnIoi_tsum_const_div_one_add_mul_pow ha ha hs 1
  simp only [pow_one] at hm
  exact (hc.add hm).congr fun x hx ↦ heq x hx.le

/-- Every alternating real derivative of a Type-I logarithmic derivative
is completely monotone on the positive axis. This is Zhang's `k = 0` family. -/
theorem IsLaguerrePolyaTypeI.isCompletelyMonotoneOnIoi_signed_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) (m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (-1 : ℝ) ^ m * iteratedDeriv m (fun y : ℝ ↦ (logDeriv f (y : ℂ)).re) x) :=
  (hf.isCompletelyMonotoneOnIoi_logDeriv h0).neg_one_pow_mul_iteratedDeriv m

end RealRooted
