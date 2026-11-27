/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Logarithmic contour deformation and radial substitution

We sum Mathlib's rectangular Cauchy theorem across adjacent sectors. The
improper radial substitution follows directly from the real Jacobian theorem.

Source: ProgramComputer, *Strict peaks in Catalan words*, coefficient formula
and finite-certificate method, ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks.LogarithmicContour

open Complex Set MeasureTheory Filter
open scoped Interval Topology

/-- The coefficient contour in logarithmic coordinates. -/
theorem circleIntegral_eq_angular (f : ℂ → ℂ) (a : ℝ) (n : ℕ) :
    (∮ z in C(0, Real.exp a), (z⁻¹) ^ (n + 1) * f z) =
      I • (∫ y : ℝ in (0)..2 * Real.pi,
        (exp ((a : ℂ) + (y : ℂ) * I))⁻¹ ^ n * f (exp ((a : ℂ) + (y : ℂ) * I))) := by
  rw [circleIntegral, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro y _
  let z := exp ((a : ℂ) + (y : ℂ) * I)
  have hz : z ≠ 0 := exp_ne_zero _
  have hy : circleMap 0 (Real.exp a) y = z := by simp [z, circleMap, exp_add, ofReal_exp]
  change deriv (circleMap 0 (Real.exp a)) y •
    ((circleMap 0 (Real.exp a) y)⁻¹ ^ (n + 1) * f (circleMap 0 (Real.exp a) y)) =
      I • (z⁻¹ ^ n * f z)
  rw [deriv_circleMap, hy]
  change (z * I) * (z⁻¹ ^ (n + 1) * f z) = I * (z⁻¹ ^ n * f z)
  rw [pow_succ]
  calc
    _ = (z * z⁻¹) * (I * (z⁻¹ ^ n * f z)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hz, one_mul]

private def sideIntegral (f : ℂ → ℂ) (a b θ : ℝ) : ℂ :=
  ∫ x in a..b, f ((x : ℂ) + (θ : ℂ) * I)

private def arcIntegral (f : ℂ → ℂ) (a θ φ : ℝ) : ℂ :=
  I • ∫ y in θ..φ, f ((a : ℂ) + (y : ℂ) * I)

private theorem rectangle {f : ℂ → ℂ} {a b θ φ : ℝ} (hab : a ≤ b) (hθφ : θ ≤ φ)
    (hc : ContinuousOn f (Icc a b ×ℂ Icc θ φ))
    (hd : DifferentiableOn ℂ f (Ioo a b ×ℂ Ioo θ φ)) :
    arcIntegral f a θ φ = arcIntegral f b θ φ +
      (sideIntegral f a b θ - sideIntegral f a b φ) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f ⟨a, θ⟩ ⟨b, φ⟩
    (by simpa [uIcc_of_le hab, uIcc_of_le hθφ] using hc)
    (by simpa [min_eq_left hab, max_eq_right hab, min_eq_left hθφ, max_eq_right hθφ] using hd)
  change sideIntegral f a b θ - sideIntegral f a b φ +
    arcIntegral f b θ φ - arcIntegral f a θ φ = 0 at h
  linear_combination -h

/-- Deform the inner angular integral to the outer arcs and the inward-to-outward
integrals of the jumps encountered at the intervening angles. -/
theorem deform {m : ℕ} {a b : ℝ} (hab : a ≤ b)
    (angle : ℕ → ℝ) (hAngle : Monotone angle)
    (sector : ℕ → ℂ → ℂ) (inner : ℝ → ℂ)
    (hc : ∀ j ≤ m, ContinuousOn (sector j)
      (Icc a b ×ℂ Icc (angle j) (angle (j + 1))))
    (hd : ∀ j ≤ m, DifferentiableOn ℂ (sector j)
      (Ioo a b ×ℂ Ioo (angle j) (angle (j + 1))))
    (hInner : ∀ j ≤ m, ∀ y ∈ Icc (angle j) (angle (j + 1)),
      sector j ((a : ℂ) + (y : ℂ) * I) = inner y)
    (hIntegrable : ∀ j ≤ m, IntervalIntegrable inner volume (angle j) (angle (j + 1)))
    (hPeriod : ∀ x ∈ Icc a b,
      sector 0 ((x : ℂ) + (angle 0 : ℂ) * I) =
        sector m ((x : ℂ) + (angle (m + 1) : ℂ) * I)) :
    I • (∫ y in (angle 0)..angle (m + 1), inner y) =
      (∑ j ∈ Finset.range (m + 1),
        I • (∫ y in angle j..angle (j + 1), sector j ((b : ℂ) + (y : ℂ) * I))) +
      ∑ j ∈ Finset.range m, (
        ∫ x in a..b, sector (j + 1) ((x : ℂ) + (angle (j + 1) : ℂ) * I) -
          sector j ((x : ℂ) + (angle (j + 1) : ℂ) * I)) := by
  let bottom (j : ℕ) := sideIntegral (sector j) a b (angle j)
  let top (j : ℕ) := sideIntegral (sector j) a b (angle (j + 1))
  have hPeriod' : bottom 0 = top m := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hPeriod x hx
  have hAdj : ∀ j, angle j ≤ angle (j + 1) := fun j => hAngle (Nat.le_succ j)
  have hSideInt (j : ℕ) (hj : j ≤ m) (y : ℝ) (hy : y ∈ Icc (angle j) (angle (j + 1))) :
      IntervalIntegrable (fun x : ℝ => sector j ((x : ℂ) + (y : ℂ) * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply (hc j hj).comp (by fun_prop)
    intro x hx
    simpa only [mem_reProdIm, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      add_im, mul_I_im, zero_add] using And.intro hx hy
  have hArc (j : ℕ) (hj : j < m + 1) :
      I • (∫ y in angle j..angle (j + 1), inner y) =
        arcIntegral (sector j) b (angle j) (angle (j + 1)) + (bottom j - top j) := by
    have hEq : arcIntegral (sector j) a (angle j) (angle (j + 1)) =
        I • (∫ y in angle j..angle (j + 1), inner y) :=
      congrArg (fun x : ℂ => I • x) <| intervalIntegral.integral_congr <|
        fun y hy => hInner j (Nat.le_of_lt_succ hj) y (uIcc_of_le (hAdj j) ▸ hy)
    rw [← hEq]
    exact rectangle hab (hAdj j) (hc j (Nat.le_of_lt_succ hj)) (hd j (Nat.le_of_lt_succ hj))
  have hJumps :
      (∑ j ∈ Finset.range (m + 1), (bottom j - top j)) =
        ∑ j ∈ Finset.range m, (∫ x in a..b,
          sector (j + 1) ((x : ℂ) + (angle (j + 1) : ℂ) * I) -
            sector j ((x : ℂ) + (angle (j + 1) : ℂ) * I)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_succ' bottom, Finset.sum_range_succ top,
      hPeriod', add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < m := Finset.mem_range.mp hj
    symm
    exact intervalIntegral.integral_sub
      (hSideInt (j + 1) (Nat.succ_le_of_lt hj') _ ⟨le_rfl, hAdj _⟩)
      (hSideInt j hj'.le _ ⟨hAdj _, le_rfl⟩)
  calc
    _ = ∑ j ∈ Finset.range (m + 1), I • (∫ y in angle j..angle (j + 1), inner y) := by
      rw [← intervalIntegral.sum_integral_adjacent_intervals
        (fun j hj => hIntegrable j (Nat.le_of_lt_succ hj)), Finset.smul_sum]
    _ = ∑ j ∈ Finset.range (m + 1),
        (arcIntegral (sector j) b (angle j) (angle (j + 1)) + (bottom j - top j)) :=
      Finset.sum_congr rfl fun j hj => hArc j (Finset.mem_range.mp hj)
    _ = _ := by
      rw [Finset.sum_add_distrib, hJumps]
      rfl

private lemma logRadius_image {R : ℝ} (hR : 0 < R) :
    (fun s : ℝ ↦ Real.log (R * (1 + s))) '' Ioi 0 = Ioi (Real.log R) := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    change 0 < s at hs
    exact Real.log_lt_log hR (by nlinarith)
  · intro hx
    have he : R < Real.exp x := by
      rw [← Real.exp_log hR]
      exact Real.exp_lt_exp.mpr hx
    refine ⟨Real.exp x / R - 1, sub_pos.mpr ((one_lt_div hR).mpr he), ?_⟩
    change Real.log (R * (1 + (Real.exp x / R - 1))) = x
    rw [show R * (1 + (Real.exp x / R - 1)) = Real.exp x by field_simp; ring,
      Real.log_exp]

/-- The outward logarithmic substitution preserves integrability and the improper integral. -/
theorem integral_logRadius_improper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {g : ℝ → E} (hInt : IntegrableOn g (Ioi (Real.log R))) :
    let transport : ℝ → E := fun s ↦ (1 + s)⁻¹ • g (Real.log (R * (1 + s)))
    IntegrableOn transport (Ioi 0) ∧
      (∫ x in Ioi (Real.log R), g x) = ∫ s in Ioi 0, transport s := by
  let f : ℝ → ℝ := fun s ↦ Real.log (R * (1 + s))
  have hf : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt f ((1 + s)⁻¹) (Ioi 0) s := by
    intro s hs
    change 0 < s at hs
    change HasDerivWithinAt (fun t : ℝ ↦ Real.log (R * (1 + t))) _ _ _
    have hp : 0 < 1 + s := by linarith [hs]
    convert ((((hasDerivAt_id s).const_add 1).const_mul R).log
      (mul_pos hR hp).ne').hasDerivWithinAt using 1
    · simp only [id_eq]
    · simp [div_mul_eq_div_div, hR.ne']
  have hi : InjOn f (Ioi 0) := by
    intro s hs t ht h
    change 0 < s at hs
    change 0 < t at ht
    have hp : 0 < R * (1 + s) := mul_pos hR (by linarith [hs])
    have hq : 0 < R * (1 + t) := mul_pos hR (by linarith [ht])
    have he := (Real.log_injOn_pos hp hq h)
    dsimp [f] at h
    nlinarith
  have he : f '' Ioi 0 = Ioi (Real.log R) := logRadius_image hR
  have habs (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : |(1 + s)⁻¹| = (1 + s)⁻¹ :=
    abs_of_pos (inv_pos.mpr (by linarith [show 0 < s from hs]))
  rw [← he] at hInt ⊢
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hf hi g).mp hInt).congr_fun
      (fun s hs ↦ congrArg (· • g (f s)) (habs s hs)) measurableSet_Ioi
  · rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf hi]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun s hs ↦ congrArg (· • g (f s)) (habs s hs))

end RealRooted.CatalanWordPeaks.LogarithmicContour
