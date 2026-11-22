/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Normalized increments from square-root logarithmic error bounds

A bound for `f x - x` gives a uniform bound for normalized increments of `f`
on `[X, X + H]`. For `H = sqrt X * log X ^ 3`, a square-root logarithmic-square
error becomes `O(1 / log X)`. The admissibility condition `H ≤ X` is eventual.
-/

public section

open Filter Set
open scoped Topology

namespace Real

/-- Errors at the two endpoints control a normalized increment. -/
theorem abs_increment_div_sub_le {f : ℝ → ℝ} {X H u E₀ E₁ : ℝ}
    (hH : 0 < H) (h₀ : |f X - X| ≤ E₀)
    (h₁ : |f (X + H * u) - (X + H * u)| ≤ E₁) :
    |(f (X + H * u) - f X) / H - u| ≤ (E₁ + E₀) / H := by
  have heq : (f (X + H * u) - f X) / H - u =
      ((f (X + H * u) - (X + H * u)) - (f X - X)) / H := by
    field_simp [hH.ne']; ring
  rw [heq, abs_div, abs_of_pos hH]
  apply div_le_div_of_nonneg_right _ hH.le
  have htri : |(f (X + H * u) - (X + H * u)) - (f X - X)| ≤
      |f (X + H * u) - (X + H * u)| + |f X - X| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (f (X + H * u) - (X + H * u)) (-(f X - X))
  exact htri.trans (add_le_add h₁ h₀)

/-- The square-root logarithmic-square weight increases by at most a factor
of eight between `X` and `2 * X`, for `X ≥ 2`. -/
theorem sqrt_mul_log_sq_le_of_le_two_mul {X Y : ℝ}
    (hX : 2 ≤ X) (hXY : X ≤ Y) (hY : Y ≤ 2 * X) :
    sqrt Y * log Y ^ 2 ≤ 8 * (sqrt X * log X ^ 2) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := hX0.trans_le hXY
  have hlogY : 0 ≤ log Y := log_nonneg (by linarith)
  have hlogs : log Y ≤ 2 * log X := by
    calc
      log Y ≤ log (2 * X) := log_le_log hY0 hY
      _ = log 2 + log X := log_mul (by norm_num) hX0.ne'
      _ ≤ 2 * log X := by linarith [log_le_log (by norm_num : (0 : ℝ) < 2) hX]
  have hsqrt : sqrt Y ≤ 2 * sqrt X := by
    calc
      sqrt Y ≤ sqrt (4 * X) := sqrt_le_sqrt (by linarith)
      _ = 2 * sqrt X := by
        rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        exact (sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hsquare : log Y ^ 2 ≤ (2 * log X) ^ 2 :=
    pow_le_pow_left₀ hlogY hlogs 2
  calc
    sqrt Y * log Y ^ 2 ≤ (2 * sqrt X) * (2 * log X) ^ 2 :=
      mul_le_mul hsqrt hsquare (sq_nonneg _) (by positivity)
    _ = 8 * (sqrt X * log X ^ 2) := by ring

/-- A square-root logarithmic-square error controls all increments in a window
of length at most `X`, uniformly over the normalized endpoint `u ∈ [0, 1]`. -/
theorem abs_increment_div_sub_le_of_sqrt_log_sq
    {f : ℝ → ℝ} {A K X H u : ℝ} (hK : 0 ≤ K)
    (herr : ∀ y : ℝ, A ≤ y → |f y - y| ≤ K * (sqrt y * log y ^ 2))
    (hAX : A ≤ X) (hX : 2 ≤ X) (hH : 0 < H) (hHX : H ≤ X)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    |(f (X + H * u) - f X) / H - u| ≤
      9 * K * (sqrt X * log X ^ 2) / H := by
  have hXY : X ≤ X + H * u := by nlinarith [hu.1]
  have hY : X + H * u ≤ 2 * X := by nlinarith [hu.2]
  have hright : |f (X + H * u) - (X + H * u)| ≤
      8 * K * (sqrt X * log X ^ 2) := by
    calc
      _ ≤ K * (sqrt (X + H * u) * log (X + H * u) ^ 2) :=
        herr _ (hAX.trans hXY)
      _ ≤ K * (8 * (sqrt X * log X ^ 2)) :=
        mul_le_mul_of_nonneg_left (sqrt_mul_log_sq_le_of_le_two_mul hX hXY hY) hK
      _ = 8 * K * (sqrt X * log X ^ 2) := by ring
  calc
    _ ≤ (8 * K * (sqrt X * log X ^ 2) + K * (sqrt X * log X ^ 2)) / H :=
      abs_increment_div_sub_le hH (herr X hAX) hright
    _ = 9 * K * (sqrt X * log X ^ 2) / H := by ring

/-- The interval length `sqrt X * log X ^ 3` is eventually positive and at most `X`. -/
theorem eventually_sqrt_mul_log_cube_pos_le :
    ∀ᶠ X : ℝ in atTop, 0 < sqrt X * log X ^ 3 ∧ sqrt X * log X ^ 3 ≤ X := by
  have hlim : Tendsto (fun X : ℝ ↦ log X ^ 3 / sqrt X) atTop (𝓝 0) := by
    simpa only [rpow_ofNat, ← sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 3 (by norm_num)).tendsto_div_nhds_zero
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlim.eventually (gt_mem_nhds one_pos)]
    with X hX hratio
  have hX0 : 0 < X := by linarith
  have hsqrt : 0 < sqrt X := sqrt_pos.mpr hX0
  have hlog : 0 < log X := log_pos hX
  have hlog_le : log X ^ 3 ≤ sqrt X := (div_le_one hsqrt).mp hratio.le
  refine ⟨by positivity, ?_⟩
  calc
    sqrt X * log X ^ 3 ≤ sqrt X * sqrt X :=
      mul_le_mul_of_nonneg_left hlog_le hsqrt.le
    _ = X := mul_self_sqrt hX0.le

/-- With window length `sqrt X * log X ^ 3`, a square-root logarithmic-square
error gives the uniform discrepancy bound `9 * K / log X`. -/
theorem eventually_increment_div_sqrt_log_cube_le
    {f : ℝ → ℝ} {A K : ℝ} (hK : 0 ≤ K)
    (herr : ∀ y : ℝ, A ≤ y → |f y - y| ≤ K * (sqrt y * log y ^ 2)) :
    ∀ᶠ X : ℝ in atTop, ∀ u ∈ Icc (0 : ℝ) 1,
      |(f (X + (sqrt X * log X ^ 3) * u) - f X) / (sqrt X * log X ^ 3) - u| ≤
        9 * K / log X := by
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop (2 : ℝ),
    eventually_sqrt_mul_log_cube_pos_le] with X hAX hX hH u hu
  have hX0 : 0 < X := by linarith
  have hsqrt : sqrt X ≠ 0 := (sqrt_pos.mpr hX0).ne'
  have hlog : log X ≠ 0 := (log_pos (by linarith : 1 < X)).ne'
  calc
    _ ≤ 9 * K * (sqrt X * log X ^ 2) / (sqrt X * log X ^ 3) :=
      abs_increment_div_sub_le_of_sqrt_log_sq hK herr hAX hX hH.1 hH.2 hu
    _ = 9 * K / log X := by field_simp [hsqrt, hlog]

/-- The normalized increments converge uniformly to the identity on `[0, 1]`
when the initial error is bounded by a square-root logarithmic-square weight. -/
theorem tendstoUniformlyOn_increment_div_sqrt_log_cube
    {f : ℝ → ℝ} {A K : ℝ} (hK : 0 ≤ K)
    (herr : ∀ y : ℝ, A ≤ y → |f y - y| ≤ K * (sqrt y * log y ^ 2)) :
    TendstoUniformlyOn
      (fun X u : ℝ ↦
        (f (X + (sqrt X * log X ^ 3) * u) - f X) / (sqrt X * log X ^ 3))
      (fun u ↦ u) atTop (Icc (0 : ℝ) 1) := by
  have hlim : Tendsto (fun X : ℝ ↦ 9 * K / log X) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_increment_div_sqrt_log_cube_le hK herr,
    hlim.eventually (gt_mem_nhds hε)] with X hbound hsmall u hu
  rw [Real.dist_eq, abs_sub_comm]
  exact (hbound u hu).trans_lt hsmall

end Real
