/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Finite differences of the first-order Riesz kernel

For the kernel `x ^ (s + 1) / (s * (s + 1))`, differences in the positive real
variable satisfy two complementary bounds. Differentiating first gives decay
`1 / ‖s‖`, uniformly in the difference step. Bounding the two endpoints gives
decay `1 / (‖s‖ * ‖s + 1‖)`, with an additional inverse step.

The combined bound applies to normalized forward and backward differences for
`0 < h ≤ x / 2`. The hypotheses `0 ≤ s.re ≤ 1` include the critical line and
every positive line to its left. No zero-free or Riemann-hypothesis assumption
is used here.
-/

public section

namespace Complex

/-- Differentiating the first-order Riesz kernel removes the factor `s + 1`. -/
theorem hasDerivAt_cpow_div_mul_add_one {x : ℝ} {s : ℂ}
    (hx : x ≠ 0) (hs : s ≠ -1) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (s + 1) / (s * (s + 1)))
      ((x : ℂ) ^ s / s) x := by
  simpa only [div_div, mul_comm (s + 1) s] using
    (hasDerivAt_ofReal_cpow_const' hx hs).div_const s

/-- The Riesz kernel has a uniform Lipschitz bound on `[x / 2, 2 * x]`. -/
theorem norm_sub_cpow_div_mul_add_one_le_mul {x y z : ℝ} {s : ℂ}
    (hx : 0 < x) (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1)
    (hy : y ∈ Set.Icc (x / 2) (2 * x))
    (hz : z ∈ Set.Icc (x / 2) (2 * x)) :
    ‖(y : ℂ) ^ (s + 1) / (s * (s + 1)) -
      (z : ℂ) ^ (s + 1) / (s * (s + 1))‖ ≤
        (2 * x ^ s.re / ‖s‖) * |y - z| := by
  have hs : s ≠ -1 := by
    intro h
    have : s.re = -1 := by simp [h]
    linarith
  have hd (u : ℝ) (hu : u ∈ Set.Icc (x / 2) (2 * x)) :
      HasDerivWithinAt
        (fun v : ℝ ↦ (v : ℂ) ^ (s + 1) / (s * (s + 1)))
        ((u : ℂ) ^ s / s) (Set.Icc (x / 2) (2 * x)) u := by
    have hu₀ : 0 < u := by linarith [hu.1]
    exact (hasDerivAt_cpow_div_mul_add_one hu₀.ne' hs).hasDerivWithinAt
  have hb (u : ℝ) (hu : u ∈ Set.Icc (x / 2) (2 * x)) :
      ‖(u : ℂ) ^ s / s‖ ≤ 2 * x ^ s.re / ‖s‖ := by
    have hu₀ : 0 < u := by linarith [hu.1]
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hu₀]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_two_mul_rpow_of_le_two_mul hu₀.le hu.2 hs₀ hs₁)
      (norm_nonneg _)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (x / 2) (2 * x)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hd hb hz hy

/-- On a fixed multiplicative neighborhood, the kernel has quadratic denominator decay. -/
theorem norm_cpow_div_mul_add_one_le {x y : ℝ} {s : ℂ}
    (hx : 0 < x) (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1)
    (hy : y ∈ Set.Icc (x / 2) (2 * x)) :
    ‖(y : ℂ) ^ (s + 1) / (s * (s + 1))‖ ≤
      4 * x ^ (s.re + 1) / (‖s‖ * ‖s + 1‖) := by
  have hy₀ : 0 < y := by linarith [hy.1]
  have hpow : y ^ (s.re + 1) ≤ 4 * x ^ (s.re + 1) := by
    calc
      y ^ (s.re + 1) ≤ (2 * x) ^ (s.re + 1) :=
        Real.rpow_le_rpow hy₀.le hy.2 (by linarith)
      _ = (2 : ℝ) ^ (s.re + 1) * x ^ (s.re + 1) :=
        Real.mul_rpow (by norm_num) hx.le
      _ ≤ 4 * x ^ (s.re + 1) := by
        have htwo : (2 : ℝ) ^ (s.re + 1) ≤ 4 := by
          calc
            (2 : ℝ) ^ (s.re + 1) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 4 := by norm_num [Real.rpow_two]
        exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hx.le _)
  rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy₀, add_re, one_re]
  exact div_le_div_of_nonneg_right hpow (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Bounding the two endpoints gives a quadratic-denominator estimate for the difference. -/
theorem norm_sub_cpow_div_mul_add_one_le {x y z : ℝ} {s : ℂ}
    (hx : 0 < x) (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1)
    (hy : y ∈ Set.Icc (x / 2) (2 * x))
    (hz : z ∈ Set.Icc (x / 2) (2 * x)) :
    ‖(y : ℂ) ^ (s + 1) / (s * (s + 1)) -
      (z : ℂ) ^ (s + 1) / (s * (s + 1))‖ ≤
        8 * x ^ (s.re + 1) / (‖s‖ * ‖s + 1‖) := by
  calc
    _ ≤ ‖(y : ℂ) ^ (s + 1) / (s * (s + 1))‖ +
        ‖(z : ℂ) ^ (s + 1) / (s * (s + 1))‖ := norm_sub_le _ _
    _ ≤ 4 * x ^ (s.re + 1) / (‖s‖ * ‖s + 1‖) +
        4 * x ^ (s.re + 1) / (‖s‖ * ‖s + 1‖) :=
      add_le_add (norm_cpow_div_mul_add_one_le hx hs₀ hs₁ hy)
        (norm_cpow_div_mul_add_one_le hx hs₀ hs₁ hz)
    _ = 8 * x ^ (s.re + 1) / (‖s‖ * ‖s + 1‖) := by ring

/-- The normalized difference satisfies both the derivative and endpoint bounds. -/
theorem norm_sub_cpow_div_mul_add_one_div_le_min {x y z h : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1)
    (hy : y ∈ Set.Icc (x / 2) (2 * x))
    (hz : z ∈ Set.Icc (x / 2) (2 * x)) (hyz : |y - z| ≤ h) :
    ‖((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
      (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ)‖ ≤
        min (2 * x ^ s.re / ‖s‖)
          (8 * x ^ (s.re + 1) / (h * ‖s‖ * ‖s + 1‖)) := by
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hh]
  apply le_min
  · calc
      _ ≤ ((2 * x ^ s.re / ‖s‖) * |y - z|) / h :=
        div_le_div_of_nonneg_right
          (norm_sub_cpow_div_mul_add_one_le_mul hx hs₀ hs₁ hy hz) hh.le
      _ ≤ ((2 * x ^ s.re / ‖s‖) * h) / h :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hyz (by positivity)) hh.le
      _ = 2 * x ^ s.re / ‖s‖ := mul_div_cancel_right₀ _ hh.ne'
  · calc
      _ ≤ (8 * x ^ (s.re + 1) / (‖s‖ * ‖s + 1‖)) / h :=
        div_le_div_of_nonneg_right
          (norm_sub_cpow_div_mul_add_one_le hx hs₀ hs₁ hy hz) hh.le
      _ = 8 * x ^ (s.re + 1) / (h * ‖s‖ * ‖s + 1‖) := by
        rw [div_div]
        congr 1
        ring

/-- A forward difference combines uniform first-order and step-dependent second-order decay. -/
theorem norm_forward_cpow_div_mul_add_one_le_min {x h : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hhx : h ≤ x / 2)
    (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1) :
    ‖(((x + h : ℝ) : ℂ) ^ (s + 1) / (s * (s + 1)) -
      (x : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ)‖ ≤
        min (2 * x ^ s.re / ‖s‖)
          (8 * x ^ (s.re + 1) / (h * ‖s‖ * ‖s + 1‖)) := by
  apply norm_sub_cpow_div_mul_add_one_div_le_min hx hh hs₀ hs₁
  · constructor <;> linarith
  · constructor <;> linarith
  · rw [add_sub_cancel_left, abs_of_pos hh]

/-- A backward difference satisfies the same two bounds as a forward difference. -/
theorem norm_backward_cpow_div_mul_add_one_le_min {x h : ℝ} {s : ℂ}
    (hx : 0 < x) (hh : 0 < h) (hhx : h ≤ x / 2)
    (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 1) :
    ‖((x : ℂ) ^ (s + 1) / (s * (s + 1)) -
      ((x - h : ℝ) : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ)‖ ≤
        min (2 * x ^ s.re / ‖s‖)
          (8 * x ^ (s.re + 1) / (h * ‖s‖ * ‖s + 1‖)) := by
  apply norm_sub_cpow_div_mul_add_one_div_le_min hx hh hs₀ hs₁
  · constructor <;> linarith
  · constructor <;> linarith
  · rw [sub_sub_cancel, abs_of_pos hh]

end Complex
