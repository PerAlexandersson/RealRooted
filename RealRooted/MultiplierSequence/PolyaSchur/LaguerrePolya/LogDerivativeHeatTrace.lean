/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.PositiveSlopeHeatTrace
public import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIFactorization
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.PowerSumMoments
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.Mathlib.Analysis.Complex.LinearProductLogDerivative
import RealRooted.Mathlib.Analysis.Complex.IteratedRealDeriv
import RealRooted.Mathlib.Analysis.CompletelyMonotone.RationalSeriesDerivatives
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.LogDeriv

/-!
# Logarithmic derivatives as Laplace transforms of zero heat traces

Zhang, arXiv:1506.07012v13, Lemma 2, equation (2.6), identifies signed
derivatives of a genus-zero product's logarithmic derivative with Laplace
moments of its zeros. The Type-I extension keeps its exponential constant.

The endpoint `x = 0` uses the checked analytic Taylor coefficient formula
and the compatibility of real and complex derivatives. Positive arguments
use local termwise differentiation of the resolvent series. Empty spectra,
zero slopes, repeated zeros, and the zeroth derivative are all included.
-/

public section

open Complex Filter MeasureTheory Topology

namespace RealRooted

/-- Every signed real derivative of the logarithmic derivative of a
summable nonnegative linear product is its zero heat-trace Laplace moment.
The real exponential contributes only to the zeroth derivative. -/
theorem signed_iteratedDeriv_re_logDeriv_exp_linear_product {c : ℂ} (hc : c ≠ 0)
    (gamma : ℝ) {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦
        (logDeriv (fun z : ℂ ↦ c * exp ((gamma : ℂ) * z) *
          ∏' i, (1 + (a i : ℂ) * z)) (y : ℂ)).re) x =
      gamma * 0 ^ k + ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-x * t) * t ^ k * Real.positiveSlopeHeatTrace a t := by
  rw [(Real.laplace_positiveSlopeHeatTrace ha hs k hx).2]
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    let F : ℂ → ℂ := fun z ↦ c * exp ((gamma : ℂ) * z) *
      ∏' i, (1 + (a i : ℂ) * z)
    have hF : Differentiable ℂ F :=
      (((differentiable_const c).mul (by fun_prop)).mul
        (Complex.differentiable_tprod_one_add_ofReal_mul hs))
    have hF0 : F 0 ≠ 0 := by simpa only [F, mul_zero, exp_zero, mul_one,
      add_zero, tprod_one] using hc
    have hreal := ((hF.analyticAt 0).logDeriv hF0).iteratedDeriv_real_of_complex k
    change (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦ (logDeriv F (y : ℂ)).re) 0 = _
    rw [hreal]
    have hcoef := signed_logDeriv_exp_linear_product hc gamma a hs k
    have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hconst : (k.factorial : ℝ) * gamma * 0 ^ k = gamma * 0 ^ k := by
      cases k <;> simp
    simp only [mul_zero, add_zero, one_pow, div_one] at ⊢
    calc (-1 : ℝ) ^ k * (iteratedDeriv k (logDeriv F) 0).re
        = (gamma * 0 ^ k + ∑' i, a i ^ (k + 1)) * (k.factorial : ℝ) :=
          (div_eq_iff hk).mp hcoef
      _ = (k.factorial : ℝ) * gamma * 0 ^ k +
          (k.factorial : ℝ) * ∑' i, a i ^ (k + 1) := by ring
      _ = _ := by rw [hconst]
  · have hlocal : (fun y : ℝ ↦
        (logDeriv (fun z : ℂ ↦ c * exp ((gamma : ℂ) * z) *
          ∏' i, (1 + (a i : ℂ) * z)) (y : ℂ)).re) =ᶠ[𝓝 x]
          (fun y : ℝ ↦ gamma + ∑' i, a i / (1 + a i * y)) :=
      Filter.Eventually.mono (isOpen_Ioi.mem_nhds hpos) fun y hy ↦
        Complex.re_logDeriv_exp_linear_product hc gamma ha hs hy.le
    rw [hlocal.iteratedDeriv_eq k]
    exact Real.neg_one_pow_mul_iteratedDeriv_const_add_tsum_resolvent ha hs gamma k hpos

/-- A Type-I function has an actual positive-zero heat trace whose Laplace
moments recover all signed logarithmic derivatives on the closed axis.
The trace and exponential constant come from the same factorization. -/
theorem IsLaguerrePolyaTypeI.exists_heatTrace_logDeriv
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0) :
    ∃ (gamma : ℝ) (a : ℕ → ℝ),
      0 ≤ gamma ∧ (∀ i, 0 ≤ a i) ∧ Summable a ∧
      f = (fun z : ℂ ↦ f 0 * exp ((gamma : ℂ) * z) * ∏' i, (1 + (a i : ℂ) * z)) ∧
      TauCeti.IsCompletelyMonotoneOnIoi (Real.positiveSlopeHeatTrace a) ∧
      ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
        IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
          Real.positiveSlopeHeatTrace a t) (Set.Ioi 0) ∧
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ ↦ (logDeriv f (y : ℂ)).re) x =
          gamma * 0 ^ k + ∫ t : ℝ in Set.Ioi 0,
            Real.exp (-x * t) * t ^ k * Real.positiveSlopeHeatTrace a t := by
  obtain ⟨gamma, a, hg, ha, hs, heq⟩ := hf.exists_eq_exp_mul_prod h0
  refine ⟨gamma, a, hg, ha, hs, heq,
    Real.isCompletelyMonotoneOnIoi_positiveSlopeHeatTrace hs, fun k x hx ↦ ?_⟩
  refine ⟨(Real.laplace_positiveSlopeHeatTrace ha hs k hx).1, ?_⟩
  have h := signed_iteratedDeriv_re_logDeriv_exp_linear_product h0 gamma ha hs k hx
  simpa only [← heq] using h

end RealRooted
