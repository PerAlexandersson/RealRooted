/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.BetaMoments
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Radial factor and covariance bounds

One product bound replaces the separately rounded first-four-moment constants.
Each factor is bounded uniformly in n by its value at 150.
The pointwise square-root and reciprocal estimates share this numerical module.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

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

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.BetaMoments

/-- The average of the one-step tilt. -/
def tiltAverage (n : ℕ) : ℝ := ((n : ℝ) - 1 / 2) / ((n : ℝ) + 1)

/-- The integrated moment envelope for the centered tilt on the local interval. -/
def tiltedMoment (n j : ℕ) : ℝ :=
  moment n (j + 1) + (3 / (2 * (n : ℝ))) * moment n j

private def scaledMoment (n j : ℕ) : ℝ := (n : ℝ) ^ j * moment n j

private def upperMoment (j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range j, ((k : ℝ) + 3 / 2) * (150 / (150 - k - 3 / 2))

private lemma scaledMoment_le {n j : ℕ} (hn : 150 ≤ n) (hj : j ≤ 4) :
    scaledMoment n j ≤ upperMoment j := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  rw [scaledMoment, upperMoment, moment_product (by linarith)]
  calc
    _ = ∏ k ∈ Finset.range j, (n : ℝ) *
        (((k : ℝ) + 3 / 2) / ((n : ℝ) - k - 3 / 2)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ _ := by
      have hkR (k : ℕ) (hk : k ∈ Finset.range j) : (k : ℝ) + 1 ≤ j := by
        exact_mod_cast (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hk))
      apply Finset.prod_le_prod₀
      · intro k hk
        have hd : 0 < (n : ℝ) - k - 3 / 2 := by linarith [hkR k hk]
        positivity
      · intro k hk
        have hd : 0 < (n : ℝ) - k - 3 / 2 := by linarith [hkR k hk]
        have hD : 0 < (150 : ℝ) - k - 3 / 2 := by linarith [hkR k hk]
        have hr : (n : ℝ) / ((n : ℝ) - k - 3 / 2) ≤ 150 / (150 - k - 3 / 2) := by
          apply (div_le_div_iff₀ hd hD).mpr
          nlinarith [mul_nonneg (sub_nonneg.mpr hnR)
            (show 0 ≤ (k : ℝ) + 3 / 2 by positivity)]
        calc
          _ = ((k : ℝ) + 3 / 2) * ((n : ℝ) / ((n : ℝ) - k - 3 / 2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

private lemma scaled_bounds {n : ℕ} (hn : 150 ≤ n) :
    scaledMoment n 1 ≤ upperMoment 1 ∧ scaledMoment n 2 ≤ upperMoment 2 ∧
      scaledMoment n 3 ≤ upperMoment 3 ∧ scaledMoment n 4 ≤ upperMoment 4 :=
  ⟨scaledMoment_le hn (by decide), scaledMoment_le hn (by decide),
    scaledMoment_le hn (by decide), scaledMoment_le hn (by decide)⟩

private theorem scaled_tiltedMoment {n : ℕ} (hn : 150 ≤ n) (j : ℕ) :
    (n : ℝ) ^ (j + 1) * tiltedMoment n j =
      scaledMoment n (j + 1) + (3 / 2) * scaledMoment n j := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (n : ℝ) ≠ 0 := by linarith
  unfold scaledMoment tiltedMoment
  rw [pow_succ]
  field_simp [hx]

private lemma scaled_tilted_le {n j : ℕ} (hn : 150 ≤ n) (hj : j ≤ 3) :
    (n : ℝ) ^ (j + 1) * tiltedMoment n j ≤
      upperMoment (j + 1) + (3 / 2) * upperMoment j := by
  rw [scaled_tiltedMoment hn]
  exact add_le_add (scaledMoment_le hn (by lia))
    (mul_le_mul_of_nonneg_left (scaledMoment_le hn (by lia)) (by norm_num))

private lemma scaled_tilted_bounds {n : ℕ} (hn : 150 ≤ n) :
    (n : ℝ) ^ 2 * tiltedMoment n 1 ≤ upperMoment 2 + (3 / 2) * upperMoment 1 ∧
      (n : ℝ) ^ 3 * tiltedMoment n 2 ≤ upperMoment 3 + (3 / 2) * upperMoment 2 ∧
      (n : ℝ) ^ 4 * tiltedMoment n 3 ≤ upperMoment 4 + (3 / 2) * upperMoment 3 :=
  ⟨scaled_tilted_le hn (by decide), scaled_tilted_le hn (by decide),
    scaled_tilted_le hn (by decide)⟩

/-- On the effective range, the tilt mean exceeds 99 percent. -/
theorem tiltAverage_ge {n : ℕ} (hn : 150 ≤ n) : 99 / 100 ≤ tiltAverage n := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold tiltAverage
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

/-- The numerical bound contributed by the Lipschitz factor after applying the tilt. -/
theorem conjugate_moment_gap_bound {n : ℕ} (hn : 150 ≤ n) :
    ((n : ℝ) / 8) * (moment n 1 - moment (n + 1) 1) ≤ 1 / (4 * (n : ℝ)) := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn' : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : 0 < (n : ℝ) - 3 / 2 := by linarith
  have h2 : 0 < (n : ℝ) - 1 / 2 := by linarith
  have hs : (3 / 2 : ℝ) < (n + 1 : ℕ) := by push_cast; linarith
  rw [moment_one (by linarith), moment_one hs, Nat.cast_add, Nat.cast_one,
    show (n : ℝ) + 1 - 3 / 2 = (n : ℝ) - 1 / 2 by ring]
  have hgap : (3 / 2 : ℝ) / ((n : ℝ) - 3 / 2) - (3 / 2) / ((n : ℝ) - 1 / 2) =
      (3 / 2) / (((n : ℝ) - 3 / 2) * ((n : ℝ) - 1 / 2)) := by
    set a := (n : ℝ) - 3 / 2
    set b := (n : ℝ) - 1 / 2
    field_simp [show a ≠ 0 from h1.ne', show b ≠ 0 from h2.ne']
    dsimp [a, b]
    ring
  rw [hgap, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos h1 h2) (by positivity)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (show 0 ≤ (n : ℝ) - 10 by linarith)]

/-- The local cubic comparison and the affine tail leave a strict margin
of at most three quarters of the target successive-size bound. -/
theorem small_covariance_numeric {n : ℕ} (hn : 150 ≤ n) :
    (11 * tiltedMoment n 1 + (1 + 11 * (n : ℝ) / 8) * tiltedMoment n 2 +
      (n : ℝ) / 8 * tiltedMoment n 3 + 1 / (20 * (n : ℝ))) / tiltAverage n <
      3 / (4 * (n : ℝ)) := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) := by linarith
  let y : ℝ := (n : ℝ)⁻¹
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1 / 150 := by
    simpa only [y, one_div] using (inv_le_inv₀ hx (by norm_num)).mpr hnR
  let T1 := (n : ℝ) ^ 2 * tiltedMoment n 1
  let T2 := (n : ℝ) ^ 3 * tiltedMoment n 2
  let T3 := (n : ℝ) ^ 4 * tiltedMoment n 3
  obtain ⟨b1, b2, b3⟩ := scaled_tilted_bounds hn
  have hEq : (n : ℝ) * (11 * tiltedMoment n 1 +
      (1 + 11 * (n : ℝ) / 8) * tiltedMoment n 2 +
      (n : ℝ) / 8 * tiltedMoment n 3 + 1 / (20 * (n : ℝ))) =
    11 * y * T1 + ((y + 11 / 8) * y) * T2 + (y ^ 2 / 8) * T3 + 1 / 20 := by
    dsimp [y, T1, T2, T3]
    field_simp [hx.ne']
  have hq : 0 < tiltAverage n := lt_of_lt_of_le (by norm_num) (tiltAverage_ge hn)
  have hA := mul_le_mul_of_nonneg_left b1 (show 0 ≤ 11 * y by positivity)
  have hB := mul_le_mul_of_nonneg_left b2 (show 0 ≤ (y + 11 / 8) * y by positivity)
  have hC := mul_le_mul_of_nonneg_left b3 (show 0 ≤ y ^ 2 / 8 by positivity)
  have hyy : y ^ 2 ≤ (1 / 150 : ℝ) ^ 2 := pow_le_pow_left₀ hy hy' 2
  norm_num [upperMoment, Finset.prod_range_succ] at hA hB hC
  have hbound : 11 * y * T1 + ((y + 11 / 8) * y) * T2 + (y ^ 2 / 8) * T3 + 1 / 20
      < (3 / 4) * tiltAverage n := by
    change 11 * y * _ ≤ _ at hA
    change ((y + 11 / 8) * y) * _ ≤ _ at hB
    change (y ^ 2 / 8) * _ ≤ _ at hC
    dsimp only [T1, T2, T3]
    nlinarith only [hA, hB, hC, hy', hyy, tiltAverage_ge hn]
  apply (div_lt_div_iff₀ hq (by positivity : 0 < 4 * (n : ℝ))).mpr
  nlinarith only [hEq, hbound]

/-- The full local quadratic comparison and the tail are below the
successive-size allowance in (12). -/
theorem broad_covariance_numeric {n : ℕ} (hn : 150 ≤ n) :
    ((((n : ℝ) / 2 + 11) * tiltedMoment n 1 +
      ((n : ℝ) / 2 + 1) * tiltedMoment n 2 + 1 / (20 * (n : ℝ))) / tiltAverage n) <
      4 / (n : ℝ) := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) := by linarith
  let y : ℝ := (n : ℝ)⁻¹
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1 / 150 := by
    simpa only [y, one_div] using (inv_le_inv₀ hx (by norm_num)).mpr hnR
  let T1 := (n : ℝ) ^ 2 * tiltedMoment n 1
  let T2 := (n : ℝ) ^ 3 * tiltedMoment n 2
  obtain ⟨b1, b2, _⟩ := scaled_tilted_bounds hn
  have hEq : (n : ℝ) * (((n : ℝ) / 2 + 11) * tiltedMoment n 1 +
      ((n : ℝ) / 2 + 1) * tiltedMoment n 2 + 1 / (20 * (n : ℝ))) =
    (1 / 2 + 11 * y) * T1 + ((1 / 2 + y) * y) * T2 + 1 / 20 := by
    dsimp [y, T1, T2]
    field_simp [hx.ne']
  have hq : 0 < tiltAverage n := lt_of_lt_of_le (by norm_num) (tiltAverage_ge hn)
  have hA := mul_le_mul_of_nonneg_left b1 (show 0 ≤ 1 / 2 + 11 * y by positivity)
  have hB := mul_le_mul_of_nonneg_left b2 (show 0 ≤ (1 / 2 + y) * y by positivity)
  have hyy : y ^ 2 ≤ (1 / 150 : ℝ) ^ 2 := pow_le_pow_left₀ hy hy' 2
  norm_num [upperMoment, Finset.prod_range_succ] at hA hB
  have hbound : (1 / 2 + 11 * y) * T1 + ((1 / 2 + y) * y) * T2 + 1 / 20 <
      4 * tiltAverage n := by
    dsimp only [T1, T2]
    nlinarith only [hA, hB, hy', hyy, tiltAverage_ge hn]
  apply (div_lt_div_iff₀ hq hx).mpr
  nlinarith only [hEq, hbound]

/-- The cubic loss in the real-part estimate (10) is below three twentieths. -/
theorem small_real_part_numeric {n : ℕ} (hn : 150 ≤ n) :
    11 * moment n 1 + (1 + 11 * (n : ℝ) / 8) * moment n 2 +
      (n : ℝ) / 8 * moment n 3 + 1 / (20 * (n : ℝ)) < 3 / 20 := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) := by linarith
  let y : ℝ := (n : ℝ)⁻¹
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1 / 150 := by
    simpa only [y, one_div] using (inv_le_inv₀ hx (by norm_num)).mpr hnR
  obtain ⟨b1, b2, b3, _⟩ := scaled_bounds hn
  have heq :
      11 * moment n 1 + (1 + 11 * (n : ℝ) / 8) * moment n 2 +
        (n : ℝ) / 8 * moment n 3 + 1 / (20 * (n : ℝ)) =
        (11 * y) * scaledMoment n 1 + (y ^ 2 + 11 * y / 8) * scaledMoment n 2 +
          (y ^ 2 / 8) * scaledMoment n 3 + y / 20 := by
    dsimp [y, scaledMoment]
    field_simp [hx.ne']
  rw [heq]
  have hA := mul_le_mul_of_nonneg_left b1 (show 0 ≤ 11 * y by positivity)
  have hB := mul_le_mul_of_nonneg_left b2 (show 0 ≤ y ^ 2 + 11 * y / 8 by positivity)
  have hC := mul_le_mul_of_nonneg_left b3 (show 0 ≤ y ^ 2 / 8 by positivity)
  have hyy : y ^ 2 ≤ (1 / 150 : ℝ) ^ 2 := pow_le_pow_left₀ hy hy' 2
  norm_num [upperMoment, Finset.prod_range_succ] at hA hB hC
  nlinarith only [hA, hB, hC, hy', hyy]

end RealRooted.CatalanWordPeaks.BetaMoments

namespace RealRooted.CatalanWordPeaks.CutBounds

private theorem factor_norm_sq_le {u g : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : g ^ 2 = 1 + u * (s : ℂ)) :
    ‖g‖ ^ 2 ≤ 1 + ‖u‖ * s := by
  rw [← norm_pow, h]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖u * (s : ℂ)‖ := norm_add_le _ _
    _ = _ := by simp [Complex.norm_real, abs_of_nonneg hs]

/-- A square-root factor grows at most linearly in the displacement. -/
theorem factor_norm_bound {u g : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : g ^ 2 = 1 + u * (s : ℂ)) :
    ‖g‖ ≤ 1 + ‖u‖ * s / 2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have H := factor_norm_sq_le hs h
  have hh := sq_nonneg (‖u‖ * s / 2)
  nlinarith

private theorem factor_difference_bound {u g : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : g ^ 2 = 1 + u * (s : ℂ)) (hr : 0 ≤ g.re) :
    ‖g - 1‖ ≤ ‖u‖ * s := by
  have hfac : (g - 1) * (g + 1) = u * (s : ℂ) := by
    calc
      _ = g ^ 2 - 1 := by ring
      _ = _ := by rw [h]; ring
  have hnorm : ‖g - 1‖ * ‖g + 1‖ = ‖u‖ * s := by
    have hh := congrArg norm hfac
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using hh
  have hreal : 1 ≤ (g + 1).re := by simpa [Complex.add_re] using hr
  have hone : 1 ≤ ‖g + 1‖ := hreal.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  calc
    _ = ‖g - 1‖ * 1 := by rw [mul_one]
    _ ≤ ‖g - 1‖ * ‖g + 1‖ := mul_le_mul_of_nonneg_left hone (norm_nonneg _)
    _ = _ := hnorm

/-- Modulus and loss bounds for two factors whose coefficients have modulus at most one. -/
theorem short_product {s : ℝ} (hs : 0 ≤ s) {u v g h : ℂ}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hg : g ^ 2 = 1 + u * (s : ℂ)) (hh : h ^ 2 = 1 + v * (s : ℂ))
    (hgr : 0 ≤ g.re) (hhr : 0 ≤ h.re) :
    ‖g * h‖ ≤ 1 + s ∧ ‖g * h - 1‖ ≤ 2 * s + s ^ 2 / 2 := by
  have hgs : ‖g‖ ^ 2 ≤ 1 + s := (factor_norm_sq_le hs hg).trans
    (by linarith [mul_le_mul_of_nonneg_right hu hs])
  have hhs : ‖h‖ ^ 2 ≤ 1 + s := (factor_norm_sq_le hs hh).trans
    (by linarith [mul_le_mul_of_nonneg_right hv hs])
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [norm_mul, mul_pow, pow_two (1 + s)]
    exact mul_le_mul hgs hhs (sq_nonneg _) (by positivity)
  · have hg₁ : ‖g - 1‖ ≤ s := (factor_difference_bound hs hg hgr).trans
      (by simpa using mul_le_mul_of_nonneg_right hu hs)
    have hh₁ : ‖h - 1‖ ≤ s := (factor_difference_bound hs hh hhr).trans
      (by simpa using mul_le_mul_of_nonneg_right hv hs)
    have hhNorm : ‖h‖ ≤ 1 + s / 2 := (factor_norm_bound hs hh).trans
      (by linarith [mul_le_mul_of_nonneg_right hv hs])
    have hdec : g * h - 1 = (g - 1) * h + (h - 1) := by ring
    calc
      _ ≤ ‖g - 1‖ * ‖h‖ + ‖h - 1‖ := by
        rw [hdec, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ s * (1 + s / 2) + s :=
        add_le_add (mul_le_mul hg₁ hhNorm (norm_nonneg _) hs) hh₁
      _ = _ := by ring

/-- The modulus and difference bounds for one long and two bounded factors. -/
theorem three_factor_majorants {s ell : ℝ} (hs : 0 ≤ s) (hell : 0 ≤ ell)
    {u₁ u₂ u₃ g₁ g₂ g₃ : ℂ} (hu₁ : ‖u₁‖ ≤ ell) (hu₂ : ‖u₂‖ ≤ 1) (hu₃ : ‖u₃‖ ≤ 1)
    (hg₁ : g₁ ^ 2 = 1 + u₁ * (s : ℂ)) (hg₂ : g₂ ^ 2 = 1 + u₂ * (s : ℂ))
    (hg₃ : g₃ ^ 2 = 1 + u₃ * (s : ℂ))
    (hr₁ : 0 ≤ g₁.re) (hr₂ : 0 ≤ g₂.re) (hr₃ : 0 ≤ g₃.re) :
    ‖g₁ * (g₂ * g₃)‖ ≤ (1 + s) * (1 + ell * s / 2) ∧
      ‖g₁ * (g₂ * g₃) - 1‖ ≤ (ell + 2) * s + (ell + 1 / 2) * s ^ 2 := by
  obtain ⟨hNorm, hDiff⟩ := short_product hs hu₂ hu₃ hg₂ hg₃ hr₂ hr₃
  have hlong := mul_le_mul_of_nonneg_right hu₁ hs
  constructor
  · rw [norm_mul, mul_comm (1 + s)]
    exact mul_le_mul ((factor_norm_bound hs hg₁).trans (by linarith [hlong]))
      hNorm (norm_nonneg _) (by positivity)
  · have hdec : g₁ * (g₂ * g₃) - 1 = (g₁ - 1) * (g₂ * g₃) + (g₂ * g₃ - 1) :=
      by ring
    calc
      _ ≤ ‖g₁ - 1‖ * ‖g₂ * g₃‖ + ‖g₂ * g₃ - 1‖ := by
        rw [hdec, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ (ell * s) * (1 + s) + (2 * s + s ^ 2 / 2) :=
        add_le_add (mul_le_mul ((factor_difference_bound hs hg₁ hr₁).trans hlong)
          hNorm (norm_nonneg _) (mul_nonneg hell hs)) hDiff
      _ = _ := by ring

/-- The reciprocal factors at the near branch point. -/
def shortReciprocal (b : ℂ) (s : ℝ) : ℂ :=
  (1 + (s : ℂ))⁻¹ * (1 + b * (s : ℂ))⁻¹

private theorem norm_one_add_lower (u : ℂ) : 1 - ‖u‖ ≤ ‖1 + u‖ := by
  simpa only [norm_one, norm_neg, sub_neg_eq_add] using norm_sub_norm_le (1 : ℂ) (-u)

private theorem reciprocal_majorants {b : ℂ} {s q : ℝ} (hs : 0 ≤ s)
    (hb : ‖b‖ ≤ 3) (hq : 0 < q) (hqs : q ≤ 1 - 3 * s) :
    ‖shortReciprocal b s‖ ≤ 1 / q ∧
      ‖shortReciprocal b s - 1‖ ≤ (3 / q + 1) * s := by
  let u := b * (s : ℂ)
  let v := (s : ℂ)
  have hu : ‖u‖ ≤ 3 * s := by
    simpa only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using
      mul_le_mul_of_nonneg_right hb hs
  have huNorm : q ≤ ‖1 + u‖ := (show q ≤ 1 - ‖u‖ by linarith).trans
    (norm_one_add_lower u)
  have huPos : 0 < ‖1 + u‖ := hq.trans_le huNorm
  have huNe : 1 + u ≠ 0 := norm_pos_iff.mp huPos
  have hvNorm : ‖1 + v‖ = 1 + s := by
    rw [show 1 + v = ((1 + s : ℝ) : ℂ) by simp [v], Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hvPos : 0 < ‖1 + v‖ := hvNorm ▸ (by positivity : 0 < 1 + s)
  have hvNe : 1 + v ≠ 0 := norm_pos_iff.mp hvPos
  have huInv : ‖(1 + u)⁻¹‖ ≤ 1 / q := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ huPos]
    rw [one_div_mul_eq_div]
    exact (one_le_div hq).mpr huNorm
  have hvInv : ‖(1 + v)⁻¹‖ ≤ 1 := by
    rw [norm_inv, hvNorm, inv_eq_one_div, div_le_one (by positivity)]
    linarith
  constructor
  · change ‖(1 + v)⁻¹ * (1 + u)⁻¹‖ ≤ 1 / q
    rw [norm_mul]
    simpa using mul_le_mul hvInv huInv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · have hInv (z : ℂ) (hz : 1 + z ≠ 0) : (1 + z)⁻¹ - 1 = -z / (1 + z) := by
      field_simp
      ring
    have hU : ‖(1 + u)⁻¹ - 1‖ ≤ (3 / q) * s := by
      rw [hInv u huNe, norm_div, norm_neg, div_le_iff₀ huPos]
      calc
        _ ≤ 3 * s := hu
        _ = ((3 / q) * s) * q := by field_simp [hq.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left huNorm (by positivity)
    have hV : ‖(1 + v)⁻¹ - 1‖ ≤ s := by
      rw [hInv v hvNe, norm_div, norm_neg, hvNorm, div_le_iff₀ (by positivity)]
      simp only [v, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      nlinarith
    change ‖(1 + v)⁻¹ * (1 + u)⁻¹ - 1‖ ≤ (3 / q + 1) * s
    have hdec :
        (1 + v)⁻¹ * (1 + u)⁻¹ - 1 =
          (1 + v)⁻¹ * ((1 + u)⁻¹ - 1) + ((1 + v)⁻¹ - 1) := by ring
    calc
      _ ≤ ‖(1 + v)⁻¹‖ * ‖(1 + u)⁻¹ - 1‖ + ‖(1 + v)⁻¹ - 1‖ := by
        rw [hdec, ← norm_mul]
        exact norm_add_le _ _
      _ ≤ 1 * ((3 / q) * s) + s :=
        add_le_add (mul_le_mul hvInv hU (norm_nonneg _) (by norm_num)) hV
      _ = _ := by ring

/-- Bounds for the reciprocal up to displacement one eighth. -/
theorem short_reciprocal_bounds {b : ℂ} {s : ℝ} (hs : 0 ≤ s) (hs₈ : s ≤ 1 / 8)
    (hb : ‖b‖ ≤ 3) :
    ‖shortReciprocal b s‖ ≤ 8 / 5 ∧ ‖shortReciprocal b s - 1‖ ≤ (29 / 5) * s := by
  have h := reciprocal_majorants hs hb (q := 5 / 8) (by norm_num) (by linarith)
  convert h using 1 <;> norm_num

/-- Bounds for the reciprocal on the longer local interval of the covariance argument. -/
theorem sixth_reciprocal_bounds {b : ℂ} {s : ℝ} (hs : 0 ≤ s) (hs₆ : s ≤ 1 / 6)
    (hb : ‖b‖ ≤ 3) :
    ‖shortReciprocal b s‖ ≤ 2 ∧ ‖shortReciprocal b s - 1‖ ≤ 7 * s := by
  have h := reciprocal_majorants hs hb (q := 1 / 2) (by norm_num) (by linarith)
  convert h using 1 <;> norm_num

/-- Local integrand error before taking the beta expectation. -/
theorem near_local_error {b K : ℂ} {s ell n : ℝ}
    (hs : 0 ≤ s) (hs₈ : s ≤ 1 / 8) (hb : ‖b‖ ≤ 3) (hell : ell ≤ n / 4)
    (hK : ‖K - 1‖ ≤ (ell + 2) * s + (ell + 1 / 2) * s ^ 2) :
    ‖shortReciprocal b s * K - 1‖ ≤ (2 * n / 5 + 9) * s +
      (2 * n / 5 + 4 / 5) * s ^ 2 := by
  let R := shortReciprocal b s
  obtain ⟨hRN, hRD⟩ := short_reciprocal_bounds hs hs₈ hb
  have hdec : R * K - 1 = R * (K - 1) + (R - 1) := by ring
  change ‖R * K - 1‖ ≤ _
  calc
    _ ≤ ‖R‖ * ‖K - 1‖ + ‖R - 1‖ := by
      rw [hdec, ← norm_mul]
      exact norm_add_le _ _
    _ ≤ (8 / 5) * ((ell + 2) * s + (ell + 1 / 2) * s ^ 2) + (29 / 5) * s :=
      add_le_add (mul_le_mul hRN hK (norm_nonneg _) (by norm_num)) hRD
    _ = (8 * ell / 5 + 9) * s + (8 * ell / 5 + 4 / 5) * s ^ 2 := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (by linarith) hs)
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end RealRooted.CatalanWordPeaks.CutBounds
