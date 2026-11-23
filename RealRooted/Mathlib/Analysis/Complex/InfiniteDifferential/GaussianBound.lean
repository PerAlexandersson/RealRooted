/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianDerivative
import RealRooted.Mathlib.Analysis.SpecialFunctions.FactorialExponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Differential-series bounds retaining the Gaussian threshold

Optimized Cauchy radii and the exponential-scale factorial bound leave a
polynomial factor times `(2*sqrt(a*b))^n`. This retains the sharp threshold
`a*b < 1/4` instead of losing an extra exponential constant.
-/

public section

namespace Complex

/-- The product of the two optimized positive Cauchy radii. -/
private theorem mul_gaussian_radius {a b : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (((n : ℝ) + 1) / (2 * a)) *
        Real.sqrt (((n : ℝ) + 1) / (2 * b)) =
      ((n : ℝ) + 1) / (2 * Real.sqrt (a * b)) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
    div_mul_div_comm, Real.mul_self_sqrt (by positivity),
    ← Real.sqrt_mul (by positivity)]
  rw [show (2 * a) * (2 * b) = 4 * (a * b) by ring,
    Real.sqrt_mul (by norm_num)]
  norm_num

/-- A Gaussian bound on the symbol at zero and on the target at the spatial
point gives a sharp geometric factor for every actual differential-series term. -/
theorem norm_differential_term_le_of_gaussian_center {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2)) (z : ℂ)
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w - z‖ ^ 2)) (n : ℕ) :
    ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤
      (2 * Real.exp 2 * Mφ * Mf) * ((n : ℝ) + 1) *
        (2 * Real.sqrt (a * b)) ^ n := by
  let r : ℝ := Real.sqrt (((n : ℝ) + 1) / (2 * a))
  let s : ℝ := Real.sqrt (((n : ℝ) + 1) / (2 * b))
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hrad : r * s = ((n : ℝ) + 1) / (2 * Real.sqrt (a * b)) :=
    mul_gaussian_radius ha.le n
  have hφn := norm_iteratedDeriv_le_of_gaussian_center hφ ha 0
    (by simpa only [sub_zero] using hφbound) n
  have hfn := norm_iteratedDeriv_le_of_gaussian_center hf hb z hfbound n
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hexp : Real.exp (((n : ℝ) + 1) / 2) * Real.exp (((n : ℝ) + 1) / 2) =
      Real.exp 1 ^ n * Real.exp 1 := by
    rw [← Real.exp_add, show ((n : ℝ) + 1) / 2 + ((n : ℝ) + 1) / 2 =
      (n : ℝ) + 1 by ring, Real.exp_add, ← Real.exp_one_pow]
  simp only [norm_div, norm_mul, norm_natCast]
  calc
    _ ≤ ((n.factorial * (Mφ * Real.exp (((n : ℝ) + 1) / 2)) / r ^ n) *
        (n.factorial * (Mf * Real.exp (((n : ℝ) + 1) / 2)) / s ^ n)) / n.factorial :=
      div_le_div_of_nonneg_right
        (mul_le_mul hφn hfn (norm_nonneg _) (by positivity)) (by positivity)
    _ = n.factorial * (Mφ * Mf) *
        (Real.exp (((n : ℝ) + 1) / 2) * Real.exp (((n : ℝ) + 1) / 2)) /
          (r * s) ^ n := by
      rw [mul_pow]
      field_simp [hfac, hr.ne', hs.ne']
    _ = (Mφ * Mf * Real.exp 1) *
        (n.factorial * (Real.exp 1 / ((n : ℝ) + 1)) ^ n) *
          (2 * Real.sqrt (a * b)) ^ n := by
      rw [hrad, hexp]
      simp only [div_pow, mul_pow]
      field_simp
    _ ≤ (Mφ * Mf * Real.exp 1) * (2 * Real.exp 1 * ((n : ℝ) + 1)) *
        (2 * Real.sqrt (a * b)) ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.factorial_mul_exp_div_pow_le n) (by positivity))
        (by positivity)
    _ = _ := by
      rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      ring

end Complex
