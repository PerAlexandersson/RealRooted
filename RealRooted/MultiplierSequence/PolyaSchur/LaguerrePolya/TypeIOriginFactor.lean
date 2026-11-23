/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.Complex.GrowthOrder
public import Mathlib.Analysis.Analytic.Order
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeICriterion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIGrowth
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Hadamard
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.Mathlib.Analysis.Complex.OriginFactor
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Factorization

/-!
# Removing the origin zero of an arbitrary nonzero Type-I function

The full analytic order at zero is extracted without increasing the growth
order. The entire cofactor retains conjugation symmetry, only real zeros,
and nonnegative Taylor data, so it remains in the Type-I class. This
discharges the structural factorization required by the origin-zero
logarithmic-derivative and heat-trace extensions.
-/

public section

namespace RealRooted

/-- Removing the complete origin zero of a nonzero Type-I function
preserves the class and every supplied order bound at most one. -/
theorem IsLaguerrePolyaTypeI.exists_origin_factor_of_order
    {f : ℂ → ℂ} {rho : ℝ} (hf : IsLaguerrePolyaTypeI f) (hfn : f ≠ 0)
    (horder : TauCeti.OrderLE f rho) (hrho : rho ≤ 1) :
    ∃ g : ℂ → ℂ, IsLaguerrePolyaTypeI g ∧ g 0 ≠ 0 ∧ TauCeti.OrderLE g rho ∧
      f = (fun z : ℂ ↦ z ^ analyticOrderNatAt f 0 * g z) := by
  have hnot : ∃ z : ℂ, f z ≠ 0 := Function.ne_iff.mp hfn
  obtain ⟨g, hgd, hg0, hgorder, hfactor⟩ :=
    horder.exists_eq_sub_pow_mul hf.toLaguerrePolya.differentiable hnot 0
  have hpow (z : ℂ) : f z = z ^ analyticOrderNatAt f 0 * g z := by
    simpa only [sub_zero] using hfactor z
  have hconj := Complex.conj_of_real_pow_mul hgd.continuous hf.toLaguerrePolya.conj
    (r := 0) (by simpa only [Complex.ofReal_zero] using hfactor)
  have hzeros (z : ℂ) (hz : g z = 0) : z.im = 0 :=
    hf.toLaguerrePolya.im_eq_zero_of_eq_zero hfn (by rw [hpow, hz, mul_zero])
  have hlp := isLaguerrePolya_of_orderLE_one (hgorder.mono hrho) hgd hg0 hconj hzeros
  have htype : IsLaguerrePolyaTypeI g :=
    hlp.isLaguerrePolyaTypeI_of_nonneg (Complex.re_iteratedDeriv_nonneg_of_pow_mul hgd hpow
      (isLaguerrePolyaTypeI_iff_isLaguerrePolya_nonneg.mp hf).2)
  exact ⟨g, htype, hg0, hgorder, funext hpow⟩

/-- Every nonzero Type-I function is an origin monomial times a Type-I
function nonzero at zero; the exponent is the actual analytic order. -/
theorem IsLaguerrePolyaTypeI.exists_origin_factor
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (hfn : f ≠ 0) :
    ∃ g : ℂ → ℂ, IsLaguerrePolyaTypeI g ∧ g 0 ≠ 0 ∧
      f = (fun z : ℂ ↦ z ^ analyticOrderNatAt f 0 * g z) := by
  obtain ⟨g, hg, hg0, _, heq⟩ := hf.exists_origin_factor_of_order hfn hf.orderLE_one le_rfl
  exact ⟨g, hg, hg0, heq⟩

end RealRooted
