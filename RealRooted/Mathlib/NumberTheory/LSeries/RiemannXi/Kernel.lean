/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.Calculus.SmoothSeries
import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay

/-!
# Positivity and decay of the Riemann theta kernel

The theta kernel with its constant term removed is positive and its derivative
is bounded above by minus pi times the kernel.
-/

@[expose] public section

open Real Filter Asymptotics Set HurwitzZeta
open scoped Topology

/-- The real theta kernel with its constant term removed. -/
noncomputable def riemannThetaKernel (t : ℝ) : ℝ := evenKernel 0 t - 1

/-- The derivative series of the theta kernel. -/
noncomputable def riemannThetaKernelDeriv (t : ℝ) : ℝ :=
  ∑' n : ℕ, -2 * π * (n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * t)

/-- The positive Gaussian series for the theta kernel. -/
theorem hasSum_riemannThetaKernel {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => 2 * exp (-π * (n + 1 : ℝ) ^ 2 * t))
      (riemannThetaKernel t) := by
  simpa [riemannThetaKernel, evenKernel_eq_cosKernel_of_zero] using hasSum_nat_cosKernel₀ 0 ht

/-- The theta kernel is strictly positive on the positive ray. -/
theorem riemannThetaKernel_pos {t : ℝ} (ht : 0 < t) : 0 < riemannThetaKernel t := by
  rw [← (hasSum_riemannThetaKernel ht).tsum_eq]
  exact lt_of_lt_of_le (by positivity)
    ((hasSum_riemannThetaKernel ht).summable.le_tsum 0 (fun _ _ => by positivity))

/-- The theta kernel is continuous on the positive ray. -/
theorem continuousOn_riemannThetaKernel : ContinuousOn riemannThetaKernel (Ioi 0) :=
  (continuousOn_evenKernel 0).sub continuousOn_const

/-- The kernel decreases faster than every real power at infinity. -/
theorem isBigO_riemannThetaKernel_rpow (r : ℝ) :
    riemannThetaKernel =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, h⟩ := isBigO_atTop_evenKernel_sub 0
  apply TauCeti.isBigO_rpow_of_isBigO_exp_neg hp one_pos (α := 1) _ r
  change (fun t => evenKernel 0 t - 1) =O[atTop] _
  simpa using h

private theorem summable_theta_weight {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * t)) := by
  have hinj : Function.Injective (fun n : ℕ => (n + 1 : ℤ)) := by
    intro a b hab
    exact_mod_cast add_right_cancel hab
  have h := (summable_pow_mul_jacobiTheta₂_term_bound 0 ht 2).comp_injective hinj
  convert h using 1
  funext n
  dsimp only [Function.comp_apply]
  push_cast
  rw [abs_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ))]
  congr 2
  ring

private theorem summable_theta_deriv {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => -2 * π * (n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * t)) := by
  simpa only [mul_assoc] using (summable_theta_weight ht).mul_left (-2 * π)

/-- Differentiation of the theta series on the positive ray. -/
theorem hasDerivAt_riemannThetaKernel {t : ℝ} (ht : 0 < t) :
    HasDerivAt riemannThetaKernel (riemannThetaKernelDeriv t) t := by
  let g (n : ℕ) (u : ℝ) := 2 * exp (-π * (n + 1 : ℝ) ^ 2 * u)
  let g' (n : ℕ) (u : ℝ) := -2 * π * (n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * u)
  have hbound := (summable_theta_weight (half_pos ht)).mul_left (2 * π)
  have hg (n : ℕ) (u : ℝ) : HasDerivAt (g n) (g' n u) u := by
    convert (((hasDerivAt_id' u).const_mul (-π * (n + 1 : ℝ) ^ 2)).exp).const_mul 2 using 1
    dsimp [g, g']
    ring
  have h := hasDerivAt_tsum_of_isPreconnected hbound isOpen_Ioi (convex_Ioi _).isPreconnected
    (fun n u _ => hg n u) (fun n u hu => ?_)
    (show t ∈ Ioi (t / 2) by change t / 2 < t; linarith)
    (hasSum_riemannThetaKernel ht).summable
    (show t ∈ Ioi (t / 2) by change t / 2 < t; linarith)
  · apply h.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact (hasSum_riemannThetaKernel hu).tsum_eq.symm
  · dsimp [g']
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos pi_pos, abs_of_nonneg (sq_nonneg _), abs_of_pos (exp_pos _)]
    simp only [mul_assoc]
    have he : exp (-π * (n + 1 : ℝ) ^ 2 * u) ≤
        exp (-π * (n + 1 : ℝ) ^ 2 * (t / 2)) := by
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hu.le
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le) (sq_nonneg _))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left he (sq_nonneg _)) pi_pos.le) (by norm_num : (0 : ℝ) ≤ 2)

/-- Each Gaussian summand decreases at least at rate pi. -/
theorem riemannThetaKernelDeriv_le {t : ℝ} (ht : 0 < t) :
    riemannThetaKernelDeriv t ≤ -π * riemannThetaKernel t := by
  rw [riemannThetaKernelDeriv, ← (hasSum_riemannThetaKernel ht).tsum_eq, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_theta_deriv ht)
    ((hasSum_riemannThetaKernel ht).summable.mul_left (-π))
  intro n
  have hn : 1 ≤ (n + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  nlinarith [mul_nonneg (mul_nonneg pi_pos.le (exp_pos (-π * (n + 1 : ℝ) ^ 2 * t)).le)
    (sub_nonneg.mpr hn)]

private theorem theta_weight_le {t : ℝ} (ht : 1 ≤ t) (n : ℕ) :
    (n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * t) ≤
      ((n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * (1 / 2))) * exp (-(π / 2) * t) := by
  conv_rhs => rw [mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply exp_le_exp.mpr
  have hn : 1 ≤ (n + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h₁ := mul_le_mul_of_nonneg_left ht (sq_nonneg (n + 1 : ℝ))
  have h₂ := mul_le_mul_of_nonneg_right hn (zero_le_one.trans ht)
  have h₃ : (n + 1 : ℝ) ^ 2 + t ≤ 2 * (n + 1 : ℝ) ^ 2 * t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h₃ pi_pos.le]

private theorem isBigO_riemannThetaKernelDeriv_exp :
    riemannThetaKernelDeriv =O[atTop] fun t => exp (-(π / 2) * t) := by
  let W (t : ℝ) := ∑' n : ℕ, (n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * t)
  have hD (t : ℝ) : riemannThetaKernelDeriv t = (-2 * π) * W t := by
    simp only [riemannThetaKernelDeriv, W, mul_assoc, tsum_mul_left]
  refine IsBigO.of_bound (2 * π * W (1 / 2)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 := zero_lt_one.trans_le ht
  have hW : W t ≤ W (1 / 2) * exp (-(π / 2) * t) := by
    dsimp only [W]
    rw [← tsum_mul_right]
    exact Summable.tsum_le_tsum (theta_weight_le ht) (summable_theta_weight ht0)
      ((summable_theta_weight (by norm_num : (0 : ℝ) < 1 / 2)).mul_right _)
  rw [hD, norm_mul, Real.norm_of_nonneg (show 0 ≤ W t from tsum_nonneg fun _ => by positivity),
    norm_mul, norm_neg, Real.norm_of_nonneg pi_pos.le, Real.norm_of_nonneg (exp_pos _).le]
  norm_num only [Real.norm_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hW (show 0 ≤ 2 * π by positivity)]

/-- The derivative kernel also decreases faster than every real power. -/
theorem isBigO_riemannThetaKernelDeriv_rpow (r : ℝ) :
    riemannThetaKernelDeriv =O[atTop] fun t => t ^ r := by
  apply TauCeti.isBigO_rpow_of_isBigO_exp_neg (half_pos pi_pos) one_pos (α := 1) _ r
  simpa using isBigO_riemannThetaKernelDeriv_exp

/-- The derivative series is continuous on the upper integration ray. -/
theorem continuousOn_riemannThetaKernelDeriv :
    ContinuousOn riemannThetaKernelDeriv (Ici 1) := by
  apply continuousOn_tsum (fun _ => by fun_prop)
    ((summable_theta_weight zero_lt_one).mul_left (2 * π))
  intro n t ht
  have he : exp (-π * (n + 1 : ℝ) ^ 2 * t) ≤ exp (-π * (n + 1 : ℝ) ^ 2 * 1) := by
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left ht
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le) (sq_nonneg _))
  have hn : -2 * π * (n + 1 : ℝ) ^ 2 * exp (-π * (n + 1 : ℝ) ^ 2 * t) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ (exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [pi_pos]) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonpos hn]
  convert mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (sq_nonneg _))
    (show 0 ≤ 2 * π by positivity) using 1
  ring
