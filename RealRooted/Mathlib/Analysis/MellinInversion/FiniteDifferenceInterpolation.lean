/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Mathlib.Analysis.MellinInversion.FiniteDifference
import RealRooted.Mathlib.Analysis.MellinInversion.Decay
import RealRooted.Mathlib.Analysis.SpecialFunctions.Pow.Interpolation

/-!
# Interpolated decay of finite differences on a positive vertical line

Interpolating the reciprocal and quadratic kernel estimates gives decay
`(1 + |t|)^(-1-p)` with coefficient `x^(c+p) / h^p` for `0 ≤ p ≤ 1`.
-/

public section

open Set

namespace Complex

/-- The reciprocal of a vertical line away from zero has uniform first-order decay. -/
theorem exists_norm_inv_line_le_rpow {c : ℝ} (hc : c ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      ‖((c : ℂ) + t * I)⁻¹‖ ≤ A * (1 + |t|) ^ (-1 : ℝ) := by
  let A : ℝ := 1 / |c| + 1
  have hc0 : 0 < |c| := abs_pos.mpr hc
  refine ⟨A, by dsimp [A]; positivity, fun t ↦ ?_⟩
  have hr : |c| ≤ ‖(c : ℂ) + t * I‖ := by
    simpa using abs_re_le_norm ((c : ℂ) + t * I)
  have hi : |t| ≤ ‖(c : ℂ) + t * I‖ := by
    simpa using abs_im_le_norm ((c : ℂ) + t * I)
  have hn : 0 < ‖(c : ℂ) + t * I‖ := hc0.trans_le hr
  have h1 : 1 ≤ ‖(c : ℂ) + t * I‖ / |c| := (one_le_div hc0).mpr hr
  have hbound : 1 + |t| ≤ A * ‖(c : ℂ) + t * I‖ := by
    calc
      _ ≤ ‖(c : ℂ) + t * I‖ / |c| + ‖(c : ℂ) + t * I‖ := by linarith
      _ = _ := by dsimp [A]; ring
  rw [norm_inv, Real.rpow_neg_one]
  calc
    ‖(c : ℂ) + t * I‖⁻¹ = 1 / ‖(c : ℂ) + t * I‖ := (one_div _).symm
    _ ≤ A / (1 + |t|) := (div_le_div_iff₀ hn (by positivity)).mpr (by simpa using hbound)
    _ = A * (1 + |t|)⁻¹ := rfl

private theorem interpolation_weight_identity {M x h w : ℝ}
    (hM : 0 < M) (hx : 0 < x) (hh : 0 < h) (hw : 0 < w) (c p : ℝ) :
    (M * x ^ c * w ^ (-1 : ℝ)) ^ (1 - p) *
      (M * x ^ (c + 1) / h * w ^ (-2 : ℝ)) ^ p =
        M * (x ^ (c + p) / h ^ p) * w ^ (-1 - p) := by
  have hU : 0 < M * x ^ c * w ^ (-1 : ℝ) := by positivity
  have hV : 0 < M * x ^ (c + 1) / h * w ^ (-2 : ℝ) := by positivity
  have hlogU : Real.log (M * x ^ c * w ^ (-1 : ℝ)) =
      Real.log M + c * Real.log x - Real.log w := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hM.ne' (by positivity),
      Real.log_rpow hx, Real.log_rpow hw]
    ring
  have hlogV : Real.log (M * x ^ (c + 1) / h * w ^ (-2 : ℝ)) =
      Real.log M + (c + 1) * Real.log x - Real.log h - 2 * Real.log w := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) hh.ne',
      Real.log_mul hM.ne' (by positivity), Real.log_rpow hx, Real.log_rpow hw]
    ring
  have hlogR : Real.log (M * (x ^ (c + p) / h ^ p) * w ^ (-1 - p)) =
      Real.log M + (c + p) * Real.log x - p * Real.log h + (-1 - p) * Real.log w := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hM.ne' (by positivity),
      Real.log_div (by positivity) (by positivity), Real.log_rpow hx,
      Real.log_rpow hh, Real.log_rpow hw]
    ring
  apply Real.log_injOn_pos (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hU,
    Real.log_rpow hV, hlogU, hlogV, hlogR]
  ring

/-- On a positive vertical line, interpolating the two finite-difference estimates gives
arbitrary intermediate denominator decay. -/
theorem exists_norm_difference_line_le_rpow {c p : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ x h y z : ℝ,
      0 < x → 0 < h → y ∈ Icc (x / 2) (2 * x) → z ∈ Icc (x / 2) (2 * x) →
      |y - z| ≤ h → ∀ t : ℝ,
      let s := (c : ℂ) + t * I
      ‖((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
        (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ)‖ ≤
          M * (x ^ (c + p) / h ^ p) * (1 + |t|) ^ (-1 - p) := by
  obtain ⟨A0, hA0, hfirst⟩ := exists_norm_inv_line_le_rpow hc0.ne'
  obtain ⟨A1, hA1, hsecond⟩ := exists_norm_inv_mul_add_one_le_rpow hc0.ne'
    (by linarith : c ≠ -1)
  let M : ℝ := 2 * A0 + 8 * A1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, fun x h y z hx hh hy hz hyz t ↦ ?_⟩
  let s : ℂ := (c : ℂ) + t * I
  let D : ℂ := ((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
    (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ)
  have hs : s.re = c := by simp [s]
  have hmin := norm_sub_cpow_div_mul_add_one_div_le_min (s := s)
    hx hh (by rw [hs]; exact hc0.le) (by rw [hs]; exact hc1) hy hz hyz
  have hU : ‖D‖ ≤ M * x ^ c * (1 + |t|) ^ (-1 : ℝ) := by
    calc
      ‖D‖ ≤ 2 * x ^ c / ‖s‖ := by simpa only [D, hs] using (le_min_iff.mp hmin).1
      _ = 2 * x ^ c * ‖s⁻¹‖ := by rw [norm_inv]; rfl
      _ ≤ 2 * x ^ c * (A0 * (1 + |t|) ^ (-1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hfirst t) (by positivity)
      _ = (2 * A0) * x ^ c * (1 + |t|) ^ (-1 : ℝ) := by ring
      _ ≤ M * x ^ c * (1 + |t|) ^ (-1 : ℝ) := by
        gcongr
        dsimp [M]
        linarith
  have hV : ‖D‖ ≤ M * x ^ (c + 1) / h * (1 + |t|) ^ (-2 : ℝ) := by
    calc
      ‖D‖ ≤ 8 * x ^ (c + 1) / (h * ‖s‖ * ‖s + 1‖) := by
        simpa only [D, hs] using (le_min_iff.mp hmin).2
      _ = (8 * x ^ (c + 1) / h) * ‖(s * (s + 1))⁻¹‖ := by
        rw [norm_inv, norm_mul]
        ring
      _ ≤ (8 * x ^ (c + 1) / h) * (A1 * (1 + |t|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hsecond t) (by positivity)
      _ = (8 * A1) * x ^ (c + 1) / h * (1 + |t|) ^ (-2 : ℝ) := by ring
      _ ≤ M * x ^ (c + 1) / h * (1 + |t|) ^ (-2 : ℝ) := by
        gcongr
        dsimp [M]
        linarith
  calc
    ‖D‖ ≤ min (M * x ^ c * (1 + |t|) ^ (-1 : ℝ))
        (M * x ^ (c + 1) / h * (1 + |t|) ^ (-2 : ℝ)) := le_min hU hV
    _ ≤ (M * x ^ c * (1 + |t|) ^ (-1 : ℝ)) ^ (1 - p) *
        (M * x ^ (c + 1) / h * (1 + |t|) ^ (-2 : ℝ)) ^ p :=
      Real.min_le_rpow_one_sub_mul_rpow (by positivity) (by positivity) hp0 hp1
    _ = M * (x ^ (c + p) / h ^ p) * (1 + |t|) ^ (-1 - p) :=
      interpolation_weight_identity hM hx hh (by positivity) c p

end Complex
