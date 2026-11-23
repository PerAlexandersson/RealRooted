/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Mellin
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.MulPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Order.IntermediateValue

/-!
# Positivity of the normalized xi coefficients

The constant coefficient is positive because xi is real and nonzero on the real
axis and equals `1/2` at one. Higher even derivatives are positive by the theta
moment bound. None of these positivity statements assumes RH.
-/

public section

open Complex
open scoped ComplexConjugate

/-- The constant normalized xi coefficient is strictly positive, unconditionally. -/
theorem riemannXiCoeff_zero_pos : 0 < riemannXiCoeff 0 := by
  rw [riemannXiCoeff_eq]
  simp only [Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, iteratedDeriv_zero]
  have hc : Continuous (fun x : ℝ => (riemannXi (x : ℂ)).re) :=
    continuous_re.comp (differentiable_riemannXi.continuous.comp continuous_ofReal)
  by_contra! h
  have hleft : (riemannXi ((1 / 2 : ℝ) : ℂ)).re ≤ 0 := by simpa using h
  have hright : 0 ≤ (riemannXi ((1 : ℝ) : ℂ)).re := by norm_num [riemannXi_one]
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hc.continuousOn ⟨hleft, hright⟩
  change (riemannXi (x : ℂ)).re = 0 at hx
  have hr : ((riemannXi (x : ℂ)).re : ℂ) = riemannXi (x : ℂ) :=
    conj_eq_iff_re.mp (by simpa using (riemannXi_conj (x : ℂ)).symm)
  exact riemannXi_ofReal_ne_zero x (by rw [← hr, hx, ofReal_zero])

/-- Differentiating the pole-removing quadratic gives the central xi derivatives. -/
theorem iteratedDeriv_riemannXi_add_two (n : ℕ) :
    iteratedDeriv (n + 2) riemannXi (1 / 2) =
      ((n + 2 : ℂ) * (n + 1) * iteratedDeriv n completedRiemannZeta₀ (1 / 2) -
        (1 / 4 : ℂ) * iteratedDeriv (n + 2) completedRiemannZeta₀ (1 / 2)) / 2 := by
  let f (z : ℂ) := completedRiemannZeta₀ (1 / 2 + z)
  have hf : Differentiable ℂ f := differentiable_completedZeta₀.comp
    (differentiable_id.const_add _)
  have heq : (fun z => riemannXi (1 / 2 + z)) = fun z =>
      (1 + (z ^ 2 * f z - (1 / 4 : ℂ) * f z)) / 2 := by
    funext z
    simp only [riemannXi, f]
    ring
  have h := congrArg (fun g : ℂ → ℂ => iteratedDeriv (n + 2) g 0) heq
  have hcf : ContDiff ℂ (n + 2) f := hf.contDiff
  simp only [iteratedDeriv_comp_const_add, add_zero] at h
  rw [iteratedDeriv_div_const, iteratedDeriv_const_add (by lia),
    iteratedDeriv_fun_sub ((by fun_prop : ContDiff ℂ (n + 2) (fun z : ℂ => z ^ 2)).mul
      hcf).contDiffAt ((contDiff_const.mul hcf).contDiffAt),
    iteratedDeriv_pow_mul_zero hf.contDiff.contDiffAt,
    iteratedDeriv_const_mul_field] at h
  have hc : ((n + 2).choose 2 : ℂ) * 2 = (n + 2 : ℂ) * (n + 1) := by
    have hn := (Nat.add_one_mul_choose_eq (n + 1) 1).symm
    exact_mod_cast (show (n + 2).choose 2 * 2 = (n + 2) * (n + 1) by
      simpa only [Nat.choose_one_right, Nat.add_assoc] using hn)
  simp only [Nat.add_sub_cancel, Nat.factorial_two, Nat.cast_ofNat, hc, f,
    iteratedDeriv_comp_const_add, add_zero] at h
  exact h

private theorem even_derivative_succ_pos (n : ℕ) :
    0 < (iteratedDeriv (2 * (n + 1)) riemannXi (1 / 2)).re := by
  have h := iteratedDeriv_riemannXi_add_two (2 * n)
  rw [show 2 * n + 2 = 2 * (n + 1) by lia,
    iteratedDeriv_completedRiemannZeta₀_even,
    iteratedDeriv_completedRiemannZeta₀_even] at h
  have hr : (iteratedDeriv (2 * (n + 1)) riemannXi (1 / 2)).re =
      ((2 * n + 2 : ℝ) * (2 * n + 1) * ((1 / 2 : ℝ) ^ (2 * n) *
        riemannXiMoment (2 * n)) - (1 / 4 : ℝ) *
          ((1 / 2 : ℝ) ^ (2 * (n + 1)) * riemannXiMoment (2 * (n + 1)))) / 2 := by
    have he := h.trans (show _ = ((((2 * n + 2 : ℝ) * (2 * n + 1) *
        ((1 / 2 : ℝ) ^ (2 * n) * riemannXiMoment (2 * n)) - (1 / 4 : ℝ) *
          ((1 / 2 : ℝ) ^ (2 * (n + 1)) * riemannXiMoment (2 * (n + 1)))) / 2 : ℝ) : ℂ) by
      push_cast
      rfl)
    exact congrArg Complex.re he
  have hbound : riemannXiMoment (2 * (n + 1)) ≤
      (2 * n + 2 : ℝ) * (2 * n + 1) * riemannXiMoment (2 * n) := by
    have h₁ := riemannXiMoment_succ_le (2 * n)
    have h₂ := riemannXiMoment_succ_le (2 * n + 1)
    have h₃ := mul_le_mul_of_nonneg_left h₁ (by positivity : (0 : ℝ) ≤ (2 * n + 1 + 1 : ℕ))
    push_cast at h₁ h₂ h₃
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by lia] at h₂
    nlinarith
  have hpos : 0 < (2 * n + 2 : ℝ) * (2 * n + 1) * riemannXiMoment (2 * n) :=
    mul_pos (by positivity) (riemannXiMoment_pos _)
  have hfactor : 0 < (1 / 2 : ℝ) ^ (2 * n) / 2 := by positivity
  have hmain : 0 < (2 * n + 2 : ℝ) * (2 * n + 1) * riemannXiMoment (2 * n) -
      riemannXiMoment (2 * (n + 1)) / 16 := by linarith
  have he : (iteratedDeriv (2 * (n + 1)) riemannXi (1 / 2)).re =
      ((1 / 2 : ℝ) ^ (2 * n) / 2) *
        ((2 * n + 2 : ℝ) * (2 * n + 1) * riemannXiMoment (2 * n) -
          riemannXiMoment (2 * (n + 1)) / 16) := by
    rw [hr]
    rw [show 2 * (n + 1) = 2 * n + 2 by lia, pow_add]
    norm_num
    ring
  rw [he]
  exact mul_pos hfactor hmain

/-- Every normalized xi coefficient is strictly positive, without assuming RH. -/
theorem riemannXiCoeff_pos (n : ℕ) : 0 < riemannXiCoeff n := by
  cases n with
  | zero => exact riemannXiCoeff_zero_pos
  | succ n =>
    rw [riemannXiCoeff_eq]
    exact mul_pos (by positivity) (even_derivative_succ_pos n)
