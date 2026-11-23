/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.IsBounded
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Ring

/-!
# Exponential lower bounds obstruct growth of order below one

A function of order below one cannot dominate a positive exponential on
the positive real ray. Entirety is not required for this growth comparison.
-/

public section

open Asymptotics Complex Filter Topology

namespace TauCeti

/-- Order below one excludes every positive exponential lower bound on
the positive real axis, even up to a multiplicative constant. -/
theorem OrderLE.not_isBigO_exp_mul_real {f : ℂ → ℂ} {rho b : ℝ}
    (hf : OrderLE f rho) (hrho : rho < 1) (hb : 0 < b) :
    ¬ (fun x : ℝ ↦ Real.exp (b * x)) =O[atTop] (fun x : ℝ ↦ f (x : ℂ)) := by
  intro hlow
  let p : ℝ := (rho + 1) / 2
  have hrp : rho < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hO := hlow.trans ((hf.isBigO hrp).comp_tendsto
    (RCLike.tendsto_ofReal_atTop_cobounded ℂ))
  simp only [Function.comp_def] at hO
  rw [Real.isBigO_exp_comp_exp_comp] at hO
  apply not_isBoundedUnder_of_tendsto_atTop _ hO
  have hsmall : Tendsto (fun x : ℝ ↦ x ^ (p - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hp1)
  have hlin : Tendsto (fun x : ℝ ↦ b / 2 * x) atTop atTop :=
    tendsto_id.const_mul_atTop (half_pos hb)
  apply tendsto_atTop_mono' atTop _ hlin
  filter_upwards [hsmall.eventually (ge_mem_nhds (half_pos hb)),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  simp only [Pi.sub_apply, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx0]
  have hid : x ^ (p - 1) * x = x ^ p := by
    calc x ^ (p - 1) * x = x ^ (p - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ p := by rw [← Real.rpow_add hx0, sub_add_cancel]
  have hmul := mul_le_mul_of_nonneg_right hx hx0.le
  rw [hid] at hmul
  linarith

end TauCeti
