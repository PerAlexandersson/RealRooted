/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic

import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The backward heat equation for entire heat sums

The entire even-derivative series satisfies the backward heat equation.
All spatial derivatives satisfy the same equation, including after restriction
to real time and taking real parts.
-/

public section

open Filter Topology

namespace Complex

/-- Differentiating a finite heat sum in time removes its constant term and
shifts the spatial derivative order by two. -/
private theorem hasDerivAt_partial_heat_succ (f : ℂ → ℂ) (z t : ℂ) (N : ℕ) :
    HasDerivAt (fun s => ∑ n ∈ Finset.range (N + 1),
      (-s) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z)
      (-(∑ n ∈ Finset.range N,
        (-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) (iteratedDeriv 2 f) z)) t := by
  have hterm (n : ℕ) : HasDerivAt
      (fun s => (-s) ^ (n + 1) / ((n + 1).factorial : ℂ) * iteratedDeriv (2 * (n + 1)) f z)
      (-((-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) (iteratedDeriv 2 f) z)) t := by
    have hb : HasDerivAt (fun s : ℂ => -s) (-1) t := by
      simpa only [Pi.neg_def, id_eq] using (hasDerivAt_id t).neg
    have h := ((hb.fun_pow (n + 1)).div_const
      ((n + 1).factorial : ℂ)).mul_const (iteratedDeriv (2 * (n + 1)) f z)
    have heq : iteratedDeriv (2 * n) (iteratedDeriv 2 f) z =
        iteratedDeriv (2 * (n + 1)) f z := by
      simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.mul_add, Nat.mul_one]
    convert h using 1
    rw [heq, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hs : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    field_simp
  have hs := (HasDerivAt.fun_sum (u := Finset.range N) (fun n _ => hterm n)).add_const (f z)
  convert hs using 1
  · ext s
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Nat.mul_zero,
      iteratedDeriv_zero, one_mul]
  · simp only [Finset.sum_neg_distrib]

/-- The entire heat operator satisfies the backward heat equation at every
complex time and spatial point. -/
theorem hasDerivAt_heatOperator_time {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (t z : ℂ) :
    HasDerivAt (fun s => heatOperator s f z) (-(iteratedDeriv 2 (heatOperator t f) z)) t := by
  have hd (N : ℕ) : Differentiable ℂ (fun s => ∑ n ∈ Finset.range N,
      (-s) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z) := by
    apply Differentiable.fun_sum
    intro n _
    exact ((differentiable_id.neg.pow n).div_const _).mul_const _
  have hconv := (tendstoLocallyUniformly_heatOperator_time hf horder hρ z).iteratedDeriv hd 1
  have hleft := ((tendstoLocallyUniformlyOn_univ.mpr hconv).tendsto_at
    (Set.mem_univ t)).comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, iteratedDeriv_one,
    (hasDerivAt_partial_heat_succ f z t _).deriv] at hleft
  have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv 2 (WithTop.coe_lt_top _)
  have hright := ((tendstoLocallyUniformlyOn_univ.mpr
    (tendstoLocallyUniformly_heatOperator_time hdf (horder.iteratedDeriv hf 2) hρ z)).tendsto_at
      (Set.mem_univ t)).neg
  have heq := tendsto_nhds_unique hleft hright
  convert (differentiable_heatOperator_time hf horder hρ z t).hasDerivAt using 1
  rw [heq, iteratedDeriv_heatOperator hf horder hρ]

/-- Every real spatial Taylor jet of the entire heat flow satisfies the
backward heat equation in real time. -/
theorem hasDerivAt_re_iteratedDeriv_heatOperator {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun s : ℝ => (iteratedDeriv n (heatOperator (s : ℂ) f) (x : ℂ)).re)
      (-(iteratedDeriv (n + 2) (heatOperator (t : ℂ) f) (x : ℂ)).re) t := by
  have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (WithTop.coe_lt_top _)
  have h := hasDerivAt_heatOperator_time hdf (horder.iteratedDeriv hf n) hρ (t : ℂ) (x : ℂ)
  have hr := h.real_of_complex
  have heq (s : ℂ) : heatOperator s (iteratedDeriv n f) = iteratedDeriv n (heatOperator s f) :=
    (iteratedDeriv_heatOperator hf horder hρ s n).symm
  simp only [heq] at hr
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
    Nat.add_comm 2, neg_re] using hr

end Complex
