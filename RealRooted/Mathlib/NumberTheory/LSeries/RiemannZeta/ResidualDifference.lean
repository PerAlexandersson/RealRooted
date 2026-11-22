/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.LogGrowth
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import RealRooted.Mathlib.Analysis.SpecialFunctions.Pow.Interpolation
import RealRooted.Mathlib.Analysis.MellinInversion.FiniteDifferenceIntegral

/-!
# Finite differences of the remaining zeta contour integral under RH

On `Re s = 9/20`, logarithmic growth is bounded by power `1/20`.
Interpolating the two kernel estimates with exponent `1/10` gives the
integrable height majorant `(1+|t|)^(-21/20)` and coefficient
`x^(11/20) / h^(1/10)`. For step `h = sqrt x`, this is exactly `sqrt x`.
-/

public section

open Complex Set MeasureTheory

namespace RiemannHypothesis

/-- The logarithmic derivative on the positive left contour line grows slower than every
positive power of the absolute height, including the compact range of heights. -/
theorem exists_norm_logDeriv_riemannZeta_le_rpow_of_pos (hRH : RiemannHypothesis)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((9 / 20 : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ r := by
  obtain ⟨B, hB, hbound⟩ := hRH.exists_norm_logDeriv_riemannZeta_le_log_add_abs
  refine ⟨B * (2 ^ r / r), by positivity, fun t ↦ ?_⟩
  calc
    _ ≤ B * Real.log (2 + |t|) := by simpa only [mul_comm] using hbound t
    _ ≤ B * ((2 ^ r / r) * (1 + |t|) ^ r) :=
      mul_le_mul_of_nonneg_left (Real.log_two_add_abs_le_mul_rpow hr t) hB.le
    _ = _ := by ring

/-- The finite-difference remainder integral on `Re s = 9/20` is genuinely integrable and
bounded by `C x^(11/20) / h^(1/10)` under RH. -/
theorem exists_norm_integral_logDeriv_difference_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x h y z : ℝ,
      0 < x → 0 < h → y ∈ Icc (x / 2) (2 * x) → z ∈ Icc (x / 2) (2 * x) →
      |y - z| ≤ h →
      let g := fun t : ℝ ↦
        let s := (9 / 20 : ℂ) + t * I
        logDeriv riemannZeta s * (((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
          (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ))
      Integrable g ∧ ‖∫ t, g t‖ ≤ C * (x ^ (11 / 20 : ℝ) / h ^ (1 / 10 : ℝ)) := by
  obtain ⟨B, _, hbound⟩ := hRH.exists_norm_logDeriv_riemannZeta_le_rpow_of_pos
    (by norm_num : (0 : ℝ) < 1 / 20)
  have hcont : Continuous (fun t : ℝ ↦
      logDeriv riemannZeta (((9 / 20 : ℝ) : ℂ) + t * I)) := by
    simpa only [mul_comm] using hRH.continuous_logDeriv_riemannZeta_line
      (σ := 9 / 20) (by norm_num) (by norm_num) (by norm_num)
  have h := Complex.exists_norm_integral_difference_line_le_rpow
    (F := logDeriv riemannZeta) (c := 9 / 20) (C := B) (r := 1 / 20) (p := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcont
    (by simpa only [ofReal_div, ofReal_ofNat] using hbound)
  simpa only [ofReal_div, ofReal_ofNat,
    show (9 / 20 : ℝ) + 1 / 10 = 11 / 20 by norm_num] using h

/-- A square-root-step finite difference of the remaining contour integral is `O(sqrt x)`
under RH, with no logarithmic loss. -/
theorem exists_norm_integral_logDeriv_sqrt_difference_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y z : ℝ, 0 < x →
      y ∈ Icc (x / 2) (2 * x) → z ∈ Icc (x / 2) (2 * x) → |y - z| ≤ Real.sqrt x →
      let g := fun t : ℝ ↦
        let s := (9 / 20 : ℂ) + t * I
        logDeriv riemannZeta s * (((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
          (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (Real.sqrt x : ℂ))
      Integrable g ∧ ‖∫ t, g t‖ ≤ C * Real.sqrt x := by
  obtain ⟨C, hC, hbound⟩ := hRH.exists_norm_integral_logDeriv_difference_le
  refine ⟨C, hC, fun x y z hx hy hz hyz ↦ ?_⟩
  have ht : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have he : x ^ (11 / 20 : ℝ) / (Real.sqrt x) ^ (1 / 10 : ℝ) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le, ← Real.rpow_sub hx]
    norm_num
  simpa only [he] using hbound x (Real.sqrt x) y z hx ht hy hz hyz

end RiemannHypothesis
