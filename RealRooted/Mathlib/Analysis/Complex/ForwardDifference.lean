/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Forward differences of Taylor derivatives

Multiplication by `exp(-z)` takes the Taylor derivatives at zero to their
forward differences. A negative real zero of an entire function with positive
real part at zero forces a negative signed forward difference of some positive
order. This conclusion uses no growth or zero-location hypothesis elsewhere.
-/

public section

open Complex Finset

namespace Complex

/-- Multiplication by the negative exponential takes Taylor derivatives to
forward differences with unit step. -/
theorem iteratedDeriv_mul_exp_neg_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun z => f z * exp (-z)) 0 =
      ((fwdDiff 1)^[n] (fun k => iteratedDeriv k f 0)) 0 := by
  rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt (by fun_prop),
    fwdDiff_iter_eq_sum_shift]
  apply sum_congr rfl
  intro k hk
  have he : (fun z : ℂ => exp (-z)) = fun z => exp ((-1 : ℂ) * z) := by
    simp
  rw [he, iteratedDeriv_cexp_const_mul]
  simp only [mul_zero, exp_zero, mul_one, nsmul_eq_mul, mul_one, zero_add, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_id]
  ring

/-- The real parts of Taylor derivatives obey the same forward-difference formula. -/
theorem re_iteratedDeriv_mul_exp_neg_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (n : ℕ) :
    (iteratedDeriv n (fun z => f z * exp (-z)) 0).re =
      ((fwdDiff 1)^[n] (fun k => (iteratedDeriv k f 0).re)) 0 := by
  rw [iteratedDeriv_mul_exp_neg_zero hf, fwdDiff_iter_eq_sum_shift,
    fwdDiff_iter_eq_sum_shift]
  simp only [Complex.re_sum]
  apply sum_congr rfl
  intro k hk
  exact map_zsmul reAddGroupHom _ _

end Complex

/-- Nonnegative real parts of the nonconstant Taylor derivatives bound an
entire function's real part below along the nonnegative real axis. -/
theorem Differentiable.re_apply_le_of_iteratedDeriv_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h : ∀ n ≠ 0, 0 ≤ (iteratedDeriv n f 0).re)
    {x : ℝ} (hx : 0 ≤ x) : (f 0).re ≤ (f x).re := by
  have hs : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * x ^ n *
      (iteratedDeriv n f 0).re) (f x).re := by
    convert Complex.hasSum_re (hasSum_taylorSeries_of_entire hf 0 (x : ℂ)) using 1
    funext n
    simp only [sub_zero, smul_eq_mul]
    rw [← ofReal_natCast, ← ofReal_inv, ← ofReal_pow, ← mul_assoc, ← ofReal_mul]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have hb := sum_le_hasSum ({0} : Finset ℕ) (fun n hn =>
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hx n))
      (h n (by simpa using hn))) hs
  simpa using hb

namespace Complex

/-- A negative real zero forces a negative signed forward difference of some
positive order in the Taylor derivatives at zero. No growth bound is required. -/
theorem exists_signed_fwdDiff_iter_neg_of_neg_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : 0 < (f 0).re) {x : ℝ}
    (hx : x < 0) (hzero : f x = 0) :
    ∃ n : ℕ, n ≠ 0 ∧
      (-1 : ℝ) ^ n * ((fwdDiff 1)^[n] (fun k => (iteratedDeriv k f 0).re)) 0 < 0 := by
  by_contra! hn
  let g : ℂ → ℂ := fun z => f (-z) * exp z
  have hg : Differentiable ℂ g := (hf.comp differentiable_neg).mul differentiable_exp
  have hderiv (n : ℕ) (hne : n ≠ 0) : 0 ≤ (iteratedDeriv n g 0).re := by
    have heq : g = fun z => (fun w => f w * exp (-w)) (-z) := by
      funext z
      simp [g]
    rw [heq]
    rw [iteratedDeriv_comp_neg n (fun w => f w * exp (-w)) 0]
    simp only [neg_zero, smul_eq_mul]
    rw [show (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) by simp,
      mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      re_iteratedDeriv_mul_exp_neg_zero hf]
    exact hn n hne
  have hb := hg.re_apply_le_of_iteratedDeriv_nonneg hderiv (neg_nonneg.mpr hx.le)
  have hz : g (-x) = 0 := by simp [g, hzero]
  have hc : g 0 = f 0 := by simp [g]
  rw [ofReal_neg, hz, hc, zero_re] at hb
  exact (not_le_of_gt h0) hb

end Complex
