/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIFactorization
import RealRooted.Mathlib.Analysis.Complex.LinearProductLowerBound

/-!
# Pure products for Type-I functions of order below one

The nonnegative exponential factor in a Type-I factorization vanishes
under a genuine growth bound of order strictly below one. Thus the product
representation used in Zhang's theorem follows without adding an assumption
that the exponential constant is zero.
-/

public section

namespace RealRooted

/-- A Type-I function nonzero at zero and of order below one is its value
at zero times a convergent product of nonnegative linear factors alone. -/
theorem IsLaguerrePolyaTypeI.exists_eq_prod_of_order_lt_one
    {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) (h0 : f 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE f rho) (hrho : rho < 1) :
    ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ Summable a ∧
      f = (fun z : ℂ ↦ f 0 * ∏' i, (1 + (a i : ℂ) * z)) := by
  obtain ⟨gamma, a, hg, ha, hs, heq⟩ := hf.exists_eq_exp_mul_prod h0
  have hgamma : gamma = 0 := Complex.eq_zero_of_exp_tprod_order_lt_one
    h0 ha hg (heq ▸ horder) hrho
  refine ⟨a, ha, hs, ?_⟩
  simpa only [hgamma, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] using heq

end RealRooted
