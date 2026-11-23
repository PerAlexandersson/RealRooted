/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import RealRooted.Mathlib.Analysis.MellinInversion.FiniteDifferenceInterpolation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Integral bounds for weighted finite differences of the Mellin kernel

A continuous line weight of growth `(1 + |t|)^r` is integrable against the
interpolated difference kernel when `r < p`. The resulting difference integral
is bounded by a constant times `x^(c+p) / h^p`.
-/

public section

open Set MeasureTheory Filter

namespace Complex

private theorem continuous_weighted_difference {F : ℂ → ℂ} {c : ℝ}
    (hc0 : 0 < c) (hF : Continuous (fun t : ℝ ↦ F ((c : ℂ) + t * I)))
    (h y z : ℝ) (hy0 : 0 < y) (hz0 : 0 < z) :
    Continuous (fun t : ℝ ↦
      let s := (c : ℂ) + t * I
      F s * (((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
        (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ))) := by
  let s (t : ℝ) : ℂ := (c : ℂ) + t * I
  let D (t : ℝ) : ℂ :=
    ((y : ℂ) ^ (s t + 1) / (s t * (s t + 1)) -
      (z : ℂ) ^ (s t + 1) / (s t * (s t + 1))) / (h : ℂ)
  have hs0 (t : ℝ) : s t ≠ 0 := by
    intro ht
    have : c = 0 := by simpa [s] using congrArg Complex.re ht
    exact hc0.ne' this
  have hs1 (t : ℝ) : s t + 1 ≠ 0 := by
    intro ht
    have : c + 1 = 0 := by simpa [s] using congrArg Complex.re ht
    linarith
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hden : Continuous (fun t ↦ s t * (s t + 1)) := hs.mul (hs.add_const 1)
  have hpow (u : ℝ) (hu : 0 < u) : Continuous (fun t : ℝ ↦ (u : ℂ) ^ (s t + 1)) :=
    (hs.add_const 1).const_cpow (Or.inl (ofReal_ne_zero.mpr hu.ne'))
  have hD : Continuous D :=
    (((hpow y hy0).div hden (fun t ↦ mul_ne_zero (hs0 t) (hs1 t))).sub
      ((hpow z hz0).div hden (fun t ↦ mul_ne_zero (hs0 t) (hs1 t)))).div_const (h : ℂ)
  exact hF.mul hD

/-- A sublinear line weight can multiply the interpolated finite-difference kernel.
The estimate retains the full step dependence and proves genuine integrability. -/
theorem exists_norm_integral_difference_line_le_rpow {F : ℂ → ℂ} {c C r p : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hrp : r < p)
    (hF : Continuous (fun t : ℝ ↦ F ((c : ℂ) + t * I)))
    (hbound : ∀ t : ℝ, ‖F ((c : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ x h y z : ℝ,
      0 < x → 0 < h → y ∈ Icc (x / 2) (2 * x) → z ∈ Icc (x / 2) (2 * x) →
      |y - z| ≤ h →
      let g := fun t : ℝ ↦
        let s := (c : ℂ) + t * I
        F s * (((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
          (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (h : ℂ))
      Integrable g ∧ ‖∫ t, g t‖ ≤ K * (x ^ (c + p) / h ^ p) := by
  obtain ⟨M, hM, hkernel⟩ := exists_norm_difference_line_le_rpow hc0 hc1 hp0 hp1
  have hC : 0 ≤ C := by
    have hb0 := hbound 0
    simpa using (norm_nonneg (F c)).trans (by simpa using hb0)
  let J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (r - 1 - p)
  have hJ0 : 0 ≤ J := integral_nonneg (fun t ↦ Real.rpow_nonneg (by positivity) _)
  have hJ : Integrable (fun t : ℝ ↦ (1 + |t|) ^ (r - 1 - p)) := by
    have hq : (1 : ℝ) < 1 + p - r := by linarith
    have hexp : -(1 + p - r) = r - 1 - p := by ring
    simpa only [Real.norm_eq_abs, hexp] using
      (integrable_one_add_norm (E := ℝ) (μ := volume)
        (r := 1 + p - r) (by simpa using hq))
  refine ⟨C * M * J + 1, by positivity, fun x h y z hx hh hy hz hyz ↦ ?_⟩
  dsimp only
  let s (t : ℝ) : ℂ := (c : ℂ) + t * I
  let D (t : ℝ) : ℂ :=
    ((y : ℂ) ^ (s t + 1) / (s t * (s t + 1)) -
      (z : ℂ) ^ (s t + 1) / (s t * (s t + 1))) / (h : ℂ)
  let a : ℝ := x ^ (c + p) / h ^ p
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpoint (t : ℝ) : ‖F (s t) * D t‖ ≤ C * M * a * (1 + |t|) ^ (r - 1 - p) := by
    rw [norm_mul]
    calc
      _ ≤ (C * (1 + |t|) ^ r) * (M * a * (1 + |t|) ^ (-1 - p)) :=
        mul_le_mul (hbound t) (hkernel x h y z hx hh hy hz hyz t)
          (norm_nonneg _) (by positivity)
      _ = C * M * a * ((1 + |t|) ^ r * (1 + |t|) ^ (-1 - p)) := by ring
      _ = C * M * a * (1 + |t|) ^ (r - 1 - p) := by
        rw [← Real.rpow_add (by positivity : 0 < 1 + |t|)]
        rw [show r + (-1 - p) = r - 1 - p by ring]
  have hcont : Continuous (fun t ↦ F (s t) * D t) :=
    continuous_weighted_difference hc0 hF h y z (by linarith [hy.1]) (by linarith [hz.1])
  have hmajor : Integrable (fun t : ℝ ↦ C * M * a * (1 + |t|) ^ (r - 1 - p)) :=
    hJ.const_mul (C * M * a)
  refine ⟨hmajor.mono' hcont.aestronglyMeasurable (Eventually.of_forall hpoint), ?_⟩
  calc
    ‖∫ t, F (s t) * D t‖ ≤ ∫ t : ℝ, C * M * a * (1 + |t|) ^ (r - 1 - p) :=
      norm_integral_le_of_norm_le hmajor (Eventually.of_forall hpoint)
    _ = C * M * a * J := by rw [integral_const_mul]
    _ ≤ (C * M * J + 1) * a := by nlinarith

end Complex
