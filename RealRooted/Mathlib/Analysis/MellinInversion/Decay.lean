/-
Copyright (c) 2026 The Tau Ceti contributors, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, RealRooted contributors
-/
module

public import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Decay of the first-order Mellin kernel

The kernel `1 / (s * (s + 1))` has quadratic decay on every vertical line avoiding its
poles. Multiplication by a continuous function of sublinear power growth preserves
absolute integrability on the line.

The denominator comparison is adapted from
`TauCeti.verticalIntegrable_inv_mul_add_one`, Tau Ceti revision
`d91980bdc255e6e50506be147ad9bcb88eb9fcc0`, `Analysis/MellinInversion.lean` (Apache-2.0).
-/

public section

open MeasureTheory Filter

namespace Complex

/-- Comparing each factor with a positive horizontal distance bounds the inverse kernel. -/
private theorem norm_inv_mul_add_one_le_inv_sq {c d : ℝ} (hd : 0 < d)
    (hdc : d ≤ |c|) (hdc1 : d ≤ |c + 1|) (t : ℝ) :
    ‖(((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹‖ ≤ (d ^ 2 + t ^ 2)⁻¹ := by
  rw [norm_inv, norm_mul]
  have hnorm (a : ℝ) (ha : d ≤ |a|) :
      Real.sqrt (d ^ 2 + t ^ 2) ≤ ‖(a : ℂ) + t * I‖ := by
    apply (Real.sqrt_le_left (norm_nonneg _)).mpr
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    nlinarith only [ha, hd.le, sq_abs a]
  have hshift : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  apply inv_anti₀ (by positivity)
  calc
    d ^ 2 + t ^ 2 = (Real.sqrt (d ^ 2 + t ^ 2)) ^ 2 :=
      (Real.sq_sqrt (by positivity)).symm
    _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      rw [sq, hshift]
      exact mul_le_mul (hnorm c hdc) (hnorm (c + 1) hdc1)
        (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The first-order Mellin kernel has quadratic decay along every line avoiding its poles. -/
theorem exists_norm_inv_mul_add_one_le_rpow {c : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      ‖(((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹‖ ≤
        A * (1 + |t|) ^ (-2 : ℝ) := by
  let d := min |c| |c + 1|
  have hd : 0 < d := lt_min (abs_pos.mpr hc)
    (abs_pos.mpr (by simpa using sub_ne_zero.mpr hc1))
  let A : ℝ := 2 / d ^ 2 + 2
  have hA : 2 ≤ A := by
    dsimp only [A]
    have : 0 ≤ 2 / d ^ 2 := by positivity
    linarith
  have hAd : 2 ≤ A * d ^ 2 := by
    dsimp only [A]
    rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero _ hd.ne')]
    nlinarith [sq_nonneg d]
  refine ⟨A, by linarith, fun t ↦ ?_⟩
  have hw : 0 < 1 + |t| := by positivity
  calc
    _ ≤ (d ^ 2 + t ^ 2)⁻¹ :=
      norm_inv_mul_add_one_le_inv_sq hd (min_le_left _ _) (min_le_right _ _) t
    _ ≤ A / (1 + |t|) ^ 2 := by
      rw [← one_div, div_le_div_iff₀ (by positivity) (sq_pos_of_pos hw)]
      nlinarith [sq_abs t, sq_nonneg (|t| - 1),
        mul_le_mul_of_nonneg_right hA (sq_nonneg t)]
    _ = A * (1 + |t|) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hw.le, Real.rpow_two]
      rfl

/-- A continuous function of power growth strictly below one can multiply the first-order
Mellin kernel without destroying absolute integrability along the vertical line. -/
theorem verticalIntegrable_div_mul_add_one_of_le_rpow {F : ℂ → ℂ} {c C r : ℝ}
    (hc : c ≠ 0) (hc1 : c ≠ -1) (hr : r < 1)
    (hF : Continuous (fun t : ℝ ↦ F ((c : ℂ) + t * I)))
    (hbound : ∀ t : ℝ, ‖F ((c : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ r) :
    VerticalIntegrable (fun s : ℂ ↦ F s / (s * (s + 1))) c := by
  obtain ⟨A, hA, hkernel⟩ := exists_norm_inv_mul_add_one_le_rpow hc hc1
  have hC : 0 ≤ C := by
    simpa using (norm_nonneg (F c)).trans (by simpa using hbound 0)
  have hmajor : Integrable (fun t : ℝ ↦ C * A * (1 + |t|) ^ (r - 2)) := by
    have h := (integrable_one_add_norm (μ := volume) (E := ℝ)
      (by simpa using (show (1 : ℝ) < 2 - r by linarith))).const_mul (C * A)
    simpa only [neg_sub, Real.norm_eq_abs] using h
  have hs0 (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
    intro h
    exact hc (by simpa using congrArg Complex.re h)
  have hs1 (t : ℝ) : (c : ℂ) + t * I + 1 ≠ 0 := by
    intro h
    have h' : c + 1 = 0 := by simpa using congrArg Complex.re h
    exact hc1 (by linarith)
  have hcont := hF.div (by fun_prop) (fun t ↦ mul_ne_zero (hs0 t) (hs1 t))
  refine hmajor.mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  dsimp only
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (C * (1 + |t|) ^ r) * (A * (1 + |t|) ^ (-2 : ℝ)) :=
      mul_le_mul (hbound t) (hkernel t) (norm_nonneg _) (by positivity)
    _ = C * A * (1 + |t|) ^ (r - 2) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add (by positivity)]
      congr 2

end Complex
