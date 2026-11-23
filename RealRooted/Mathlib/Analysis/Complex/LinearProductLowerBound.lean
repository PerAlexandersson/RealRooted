/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import Mathlib.Analysis.Complex.Exponential
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.SubexponentialLowerBound
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Positive linear products and their exponential factors

Nonnegative slopes give a product with norm at least one in the right
half-plane. Hence an entire product of order below one cannot have a
positive real exponential factor. No summability or entire-function
hypothesis is needed beyond the stated growth bound for this obstruction.
-/

public section

open Asymptotics Filter Topology

namespace Complex

/-- A product of nonnegative real linear slopes has norm at least one on
the closed right half-plane. The totalized nonmultipliable case also equals one. -/
theorem one_le_norm_tprod_one_add_ofReal_mul {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) {z : ℂ} (hz : 0 ≤ z.re) :
    1 ≤ ‖∏' i, (1 + (a i : ℂ) * z)‖ := by
  by_cases hm : Multipliable (fun i ↦ (1 + (a i : ℂ) * z))
  · apply ge_of_tendsto' hm.hasProd.norm
    intro s
    calc (1 : ℝ) = ∏ i ∈ s, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ s, ‖1 + (a i : ℂ) * z‖ := by
        apply Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one)
        intro i _
        apply le_trans _ (Complex.re_le_norm _)
        simp only [add_re, one_re, re_ofReal_mul]
        exact le_add_of_nonneg_right (mul_nonneg (ha i) hz)
  · rw [tprod_eq_one_of_not_multipliable hm, norm_one]

/-- A nonnegative real exponential factor in a positive linear product
must vanish if the product has growth order strictly below one. -/
theorem eq_zero_of_exp_tprod_order_lt_one {ι : Type*} {a : ι → ℝ}
    {c : ℂ} {gamma rho : ℝ} (hc : c ≠ 0) (ha : ∀ i, 0 ≤ a i)
    (hg : 0 ≤ gamma)
    (horder : TauCeti.OrderLE (fun z : ℂ ↦ c * exp ((gamma : ℂ) * z) *
      ∏' i, (1 + (a i : ℂ) * z)) rho) (hrho : rho < 1) : gamma = 0 := by
  apply le_antisymm _ hg
  by_contra h
  have hgpos : 0 < gamma := lt_of_not_ge h
  apply horder.not_isBigO_exp_mul_real hrho hgpos
  apply Asymptotics.IsBigO.of_bound ‖c‖⁻¹
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hP := one_le_norm_tprod_one_add_ofReal_mul ha (z := (x : ℂ)) hx
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [Real.norm_eq_abs, Real.abs_exp, norm_mul, norm_mul, norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  calc Real.exp (gamma * x)
      ≤ Real.exp (gamma * x) * ‖∏' i, (1 + (a i : ℂ) * (x : ℂ))‖ :=
        le_mul_of_one_le_right (Real.exp_nonneg _) hP
    _ = _ := by
      field_simp [hcn]
      simp only [mul_comm]

end Complex
