/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Decay of horizontal Riesz integrals

Uniform logarithmic-square growth of a multiplier is dominated by the
quadratic denominator decay of the first-order Riesz kernel. The resulting
horizontal integrals vanish at large absolute heights for every fixed `x ≥ 1`.
-/

public section

open Filter Set MeasureTheory
open scoped Topology Interval

namespace Complex

/-- A lower bound on the imaginary part controls both Riesz denominator factors. -/
theorem norm_mul_cpow_div_mul_add_one_le {F : ℂ → ℂ} {s : ℂ} {x T B b : ℝ}
    (hx : 1 ≤ x) (hT : 0 < T) (hs : s.re ≤ b) (ht : T ≤ |s.im|)
    (hF : ‖F s‖ ≤ B) :
    ‖F s * (x : ℂ) ^ (s + 1) / (s * (s + 1))‖ ≤
      B * x ^ (b + 1) / T ^ 2 := by
  have hx₀ : 0 < x := by linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans hF
  have hs₀ : T ≤ ‖s‖ := ht.trans (abs_im_le_norm s)
  have hs₁ : T ≤ ‖s + 1‖ := ht.trans (by simpa using abs_im_le_norm (s + 1))
  have hden : T ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [sq]
    exact mul_le_mul hs₀ hs₁ hT.le (norm_nonneg _)
  have hpow : x ^ (s + 1).re ≤ x ^ (b + 1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by simpa using add_le_add_right hs 1)
  rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx₀]
  exact div_le_div₀ (mul_nonneg hB (Real.rpow_nonneg hx₀.le _))
    (mul_le_mul hF hpow (Real.rpow_nonneg hx₀.le _) hB)
    (sq_pos_of_pos hT) hden

/-- A uniform multiplier bound gives an explicit bound for a horizontal integral. -/
theorem norm_horizontal_integral_le {F : ℂ → ℂ} {a b x t T B : ℝ}
    (hab : a ≤ b) (hx : 1 ≤ x) (hT : 0 < T) (ht : T ≤ |t|)
    (hF : ∀ σ ∈ Icc a b, ‖F (σ + I * t)‖ ≤ B) :
    ‖∫ σ in a..b,
      F (σ + I * t) * (x : ℂ) ^ ((σ : ℂ) + I * t + 1) /
        (((σ : ℂ) + I * t) * ((σ : ℂ) + I * t + 1))‖ ≤
      (b - a) * B * x ^ (b + 1) / T ^ 2 := by
  have hbnd : ∀ σ ∈ Ι a b,
      ‖F (σ + I * t) * (x : ℂ) ^ ((σ : ℂ) + I * t + 1) /
        (((σ : ℂ) + I * t) * ((σ : ℂ) + I * t + 1))‖ ≤
          B * x ^ (b + 1) / T ^ 2 := by
    intro σ hσ
    rw [uIoc_of_le hab] at hσ
    exact norm_mul_cpow_div_mul_add_one_le hx hT (by simpa using hσ.2)
      (by simpa using ht) (hF σ ⟨hσ.1.le, hσ.2⟩)
  calc
    _ ≤ (B * x ^ (b + 1) / T ^ 2) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    _ = (b - a) * B * x ^ (b + 1) / T ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

/-- Logarithmic-square multiplier growth still makes horizontal Riesz integrals vanish. -/
theorem tendsto_horizontal_integral_zero {ι : Type*} {l : Filter ι}
    {F : ℂ → ℂ} {a b x C : ℝ} {T t : ι → ℝ}
    (hab : a ≤ b) (hx : 1 ≤ x) (hT : Tendsto T l atTop)
    (ht : ∀ᶠ i in l, T i ≤ |t i|)
    (hF : ∀ᶠ i in l, ∀ σ ∈ Icc a b,
      ‖F (σ + I * t i)‖ ≤ C * Real.log (T i) ^ 2) :
    Tendsto (fun i ↦ ∫ σ in a..b,
      F (σ + I * t i) * (x : ℂ) ^ ((σ : ℂ) + I * t i + 1) /
        (((σ : ℂ) + I * t i) * ((σ : ℂ) + I * t i + 1))) l (𝓝 0) := by
  have hlog : Tendsto (fun y : ℝ ↦ Real.log y ^ 2 / y ^ 2) atTop (𝓝 0) := by
    simpa only [id_eq, div_pow, zero_pow (by norm_num : 2 ≠ 0)] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.pow 2
  have hlim : Tendsto
      (fun i ↦ ((b - a) * C * x ^ (b + 1)) *
        (Real.log (T i) ^ 2 / (T i) ^ 2)) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (hlog.comp hT).const_mul ((b - a) * C * x ^ (b + 1))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hT.eventually_gt_atTop 0, ht, hF] with i hi hti hFi
  calc
    _ ≤ (b - a) * (C * Real.log (T i) ^ 2) * x ^ (b + 1) / (T i) ^ 2 :=
      norm_horizontal_integral_le hab hx hi hti hFi
    _ = ((b - a) * C * x ^ (b + 1)) *
        (Real.log (T i) ^ 2 / (T i) ^ 2) := by ring

end Complex
