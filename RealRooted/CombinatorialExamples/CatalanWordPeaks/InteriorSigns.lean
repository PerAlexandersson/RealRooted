/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.PhaseSigns
import RealRooted.CombinatorialExamples.CatalanWordPeaks.NearCovariance
import Mathlib.Tactic

/-!
# The next row at old interior roots

A one-step rotation makes the signed imaginary part dominate the mean difference
and the two far-ray errors. Root enumeration uses the standard library elsewhere.

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

public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Complex Set

private theorem phase_step {d : ℝ} (hd : 0 < d) (hD : d < 1) (n : ℕ) :
    nearPhaseUnit d (n + 1) =
      ((d : ℂ) - (Real.sqrt (1 - d ^ 2) : ℂ) * I) * nearPhaseUnit d n := by
  let a := radius d
  let z := nearPoint d
  let σ := Real.sqrt (1 - d ^ 2)
  let ρ := (d : ℂ) - (σ : ℂ) * I
  let B := rayPrefactor d 0 z
  have hA : 0 < a := radius_pos hd.le
  have ha : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA.ne'
  have hz : z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simpa only [z, nearPoint_norm hd hD] using hA.ne'
  have hB : (‖B‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
    (rayPrefactor_near_ne_zero hd hD))
  have hσ : σ ^ 2 = 1 - d ^ 2 := Real.sq_sqrt (by nlinarith)
  have hprod : z * ρ = (a : ℂ) := by
    have hre : z.re = a * d := rfl
    have him : z.im = a * σ := nearPoint_im_eq hd
    apply Complex.ext
    · simp only [mul_re, mul_im, ρ, sub_re, sub_im, ofReal_re, ofReal_im,
        I_re, I_im, mul_zero, add_zero, sub_zero, mul_one, hre, him]
      linear_combination a * hσ
    · simp only [mul_im, mul_re, ρ, sub_re, sub_im, ofReal_re, ofReal_im,
        I_re, I_im, mul_zero, add_zero, sub_zero, mul_one, hre, him]
      ring
  have hρ : ρ = z⁻¹ * (a : ℂ) := by
    calc
      ρ = (z⁻¹ * z) * ρ := by rw [inv_mul_cancel₀ hz, one_mul]
      _ = z⁻¹ * (a : ℂ) := by rw [mul_assoc, hprod]
  change -(z⁻¹ ^ (n + 1)) * B / ((((a⁻¹) ^ (n + 1) * ‖B‖ : ℝ)) : ℂ) =
    ρ * (-(z⁻¹ ^ n) * B / ((((a⁻¹) ^ n * ‖B‖ : ℝ)) : ℂ))
  rw [hρ]
  push_cast
  rw [pow_succ (z⁻¹), pow_succ ((a : ℂ)⁻¹)]
  field_simp [hz, ha, hB]

private theorem im_sign_of_near_unit {u z : ℂ} {e : ℝ}
    (hu : ‖u‖ = 1) (he : e ^ 2 = 1) (heU : 0 < e * u.im)
    (hz : ‖z - u‖ < 73 / 100) (hr : |z.re| < 1 / 25) :
    0 < e * z.im := by
  by_contra! hj
  have hprod : z.im * u.im ≤ 0 := by
    calc
      _ = (e * z.im) * (e * u.im) := by
        rw [show (e * z.im) * (e * u.im) = e ^ 2 * (z.im * u.im) by ring, he, one_mul]
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hj heU.le
  have hre : z.re * u.re ≤ 1 / 25 := by
    have hu' : |u.re| ≤ 1 := (abs_re_le_norm u).trans_eq hu
    calc
      _ ≤ |z.re * u.re| := le_abs_self _
      _ = |z.re| * |u.re| := abs_mul _ _
      _ ≤ (1 / 25) * 1 := mul_le_mul hr.le hu' (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hnorm : ‖z - u‖ ^ 2 = (z.re - u.re) ^ 2 + (z.im - u.im) ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hunit : u.re ^ 2 + u.im ^ 2 = 1 := by
    calc
      _ = ‖u‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
      _ = 1 := by rw [hu]; norm_num
  have hsmall := pow_lt_pow_left₀ (n := 2) hz (norm_nonneg _) (by decide)
  nlinarith only [hnorm, hunit, hsmall, hre, hprod, sq_nonneg z.re, sq_nonneg z.im]

private theorem abs_im_lower {z : ℂ} {a b c : ℝ}
    (ha0 : 0 ≤ a) (hb : |z.re| ≤ b) (hnorm : a < ‖z‖)
    (hbound : b ^ 2 + c ^ 2 ≤ a ^ 2) : c < |z.im| := by
  by_contra! h
  have hre := pow_le_pow_left₀ (abs_nonneg z.re) hb 2
  have him := pow_le_pow_left₀ (abs_nonneg z.im) h 2
  have hnorm' := pow_lt_pow_left₀ (n := 2) hnorm ha0 (by decide)
  rw [sq_abs] at hre him
  rw [Complex.sq_norm, Complex.normSq_apply] at hnorm'
  nlinarith only [hre, him, hnorm', hbound]

private theorem near_norm_at_least_mean_re {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1) :
    (nearMean d n).re ≤ ‖nearPhaseUnit d n * nearMean d n‖ := by
  rw [norm_mul, norm_nearPhaseUnit hd hD, one_mul]
  exact (le_abs_self _).trans (abs_re_le_norm _)

private theorem near_norm_gt_twenty_seven_hundredths {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d) :
    27 / 100 < ‖nearPhaseUnit d n * nearMean d n‖ := by
  rw [norm_mul, norm_nearPhaseUnit hd hD, one_mul]
  have hclose := nearMean_close_to_one hd hD hn hS hL
  have htri := norm_sub_norm_le (1 : ℂ) (nearMean d n)
  rw [norm_one, norm_sub_rev] at htri
  linarith

/-- The one-step mean error and both far rays are smaller than the rotated imaginary part. -/
private theorem phase_step_error_lt {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hL : 29 / 10 ≤ (n : ℝ) * d)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) {err : ℝ}
    (hRe : |(nearPhaseUnit d n * nearMean d n).re| < 1 / 25)
    (herr : |err| ≤ |farRayError d n| + |farRayError d (n + 1)| +
      ‖nearMean d (n + 1) - nearMean d n‖) :
    |err| < Real.sqrt (1 - d ^ 2) * |(nearPhaseUnit d n * nearMean d n).im| := by
  let σ := Real.sqrt (1 - d ^ 2)
  let Z := nearPhaseUnit d n * nearMean d n
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hS' : 2 ≤ ((n + 1 : ℕ) : ℝ) * σ :=
    hS.trans (mul_le_mul_of_nonneg_right (by push_cast; linarith) (Real.sqrt_nonneg _))
  have hL' : 29 / 10 ≤ ((n + 1 : ℕ) : ℝ) * d :=
    hL.trans (mul_le_mul_of_nonneg_right (by push_cast; linarith) hd.le)
  have hL0 : 2 ≤ (n : ℝ) * d := by linarith
  have hr := farRayError_interior hd hD hn hL hS
  have hRe' : |Z.re| < 1 / 25 := hRe
  by_cases hdHalf : 1 / 2 ≤ d
  · have hJ := nearMean_re_gt_seventeen_twentieths hd hD hn hdHalf hS
    have him : 4 / 5 < |Z.im| := abs_im_lower (by norm_num : 0 ≤ (17 / 20 : ℝ))
      hRe'.le (hJ.trans_le (near_norm_at_least_mean_re hd hD)) (by norm_num)
    have hsmall := farRayError_smallAngle hd hD hn hdHalf hS
    have hsmall' : |farRayError d (n + 1)| < 1 / (100 * (n : ℝ)) :=
      (farRayError_smallAngle (n := n + 1) hd hD (by lia) hdHalf hS').trans_le
        (one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
    have hΔ := nearMean_step_lt_one_div hd hD hn hdHalf hS
    have hnPos : 0 < (n : ℝ) := by linarith
    have hσ : 2 / (n : ℝ) ≤ σ := (div_le_iff₀ hnPos).2 (by simpa [mul_comm] using hS)
    have hlower := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hσ him (by norm_num)
      ((by positivity : 0 < 2 / (n : ℝ)).trans_le hσ)
    apply (herr.trans_lt (add_lt_add (add_lt_add hsmall hsmall') hΔ)).trans
    apply lt_of_le_of_lt _ hlower
    rw [show 1 / (100 * (n : ℝ)) = (1 / 100) * (1 / (n : ℝ)) by ring,
      show 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) by ring]
    linarith [one_div_pos.mpr hnPos]
  · have hσ2 : σ ^ 2 = 1 - d ^ 2 := Real.sq_sqrt (by nlinarith)
    have hσ : 7 / 10 ≤ σ := by
      apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      rw [hσ2]
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr (le_of_not_ge hdHalf))]
    have him : 1 / 4 < |Z.im| := abs_im_lower (by norm_num : 0 ≤ (27 / 100 : ℝ))
      hRe'.le (near_norm_gt_twenty_seven_hundredths hd hD hn hS hL0) (by norm_num)
    have hlarge' := farRayError_largeAngle hd hD (by lia) hL' hσ
    have hΔ := nearMean_step_lt_four_div hd hD hn hS hL0
    have hΔ' : ‖nearMean d (n + 1) - nearMean d n‖ < 4 / 150 :=
      hΔ.trans_le (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)
    have hlower := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hσ him (by norm_num)
      ((by norm_num : (0 : ℝ) < 7 / 10).trans_le hσ)
    exact (herr.trans_lt (add_lt_add (add_lt_add hr hlarge') hΔ')).trans
      (lt_of_le_of_lt (by norm_num) hlower)

/-- The sign at an old zero agrees with the signed imaginary part of the unit
   phase. The radial conditions are those used for the interior checkpoints. -/
theorem eval_sign_at_oldRoot_of_phaseSign {d : ℝ} {n j : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n)
    (hL : 29 / 10 ≤ (n : ℝ) * d) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2))
    (hzero : (polynomial n).eval (1 - (scale d ^ 2)⁻¹) = 0)
    (hphase : 0 < (-1 : ℝ) ^ j * (nearPhaseUnit d n).im) :
    0 < (-1 : ℝ) ^ j * (polynomial (n + 1)).eval (1 - (scale d ^ 2)⁻¹) := by
  let e : ℝ := (-1) ^ j
  let σ := Real.sqrt (1 - d ^ 2)
  let u := nearPhaseUnit d n
  let u' := nearPhaseUnit d (n + 1)
  let J := nearMean d n
  let J' := nearMean d (n + 1)
  let Z := u * J
  let r := farRayError d n
  let r' := farRayError d (n + 1)
  let err := -d * r + r' + (u' * (J' - J)).re
  have hn0 : 0 < n := by lia
  have hL0 : 2 ≤ (n : ℝ) * d := by linarith
  have he : e ^ 2 = 1 := by
    dsimp [e]
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  have habsE : |e| = 1 := by simp [e, abs_pow]
  have hr : |r| < 1 / 25 := farRayError_interior hd hD hn hL hS
  have hRe : Z.re = -r := by
    have hnz : normalizedCoefficient d n = 0 := by
      rw [normalizedCoefficient, hzero, mul_zero, zero_div]
    rw [normalizedCoefficient_eq_near_add_far hd hD hn0] at hnz
    exact eq_neg_of_add_eq_zero_left hnz
  have hRe' : |Z.re| < 1 / 25 := by rw [hRe, abs_neg]; exact hr
  have hclose : ‖Z - u‖ < 73 / 100 := by
    rw [show Z - u = u * (J - 1) by dsimp [Z]; ring, norm_mul,
      norm_nearPhaseUnit hd hD, one_mul]
    exact nearMean_close_to_one hd hD hn hS hL0
  have hImpos : 0 < e * Z.im :=
    im_sign_of_near_unit (norm_nearPhaseUnit hd hD n) he hphase hclose hRe'
  have hIm : e * Z.im = |Z.im| := by
    rw [← one_mul |Z.im|, ← habsE, ← abs_mul, abs_of_pos hImpos]
  have hnext : normalizedCoefficient d (n + 1) = σ * Z.im + err := by
    rw [normalizedCoefficient_eq_near_add_far hd hD (Nat.succ_pos n)]
    change (u' * J').re + r' = _
    rw [show u' * J' = ((d : ℂ) - (σ : ℂ) * I) * Z + u' * (J' - J) by
      dsimp only [Z]
      rw [← mul_assoc, ← phase_step hd hD n]
      ring]
    have hrotRe : (((d : ℂ) - (σ : ℂ) * I) * Z).re =
        d * Z.re + σ * Z.im := by
      simp only [mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, mul_one, add_zero, sub_zero, zero_sub]
      ring
    rw [add_re, hrotRe, hRe]
    unfold err
    ring
  have herr : |err| ≤ |r| + |r'| + ‖J' - J‖ := by
    unfold err
    calc
      _ ≤ |-d * r + r'| + |(u' * (J' - J)).re| := abs_add_le _ _
      _ ≤ (|-d * r| + |r'|) + ‖u' * (J' - J)‖ :=
        add_le_add (abs_add_le _ _) (abs_re_le_norm _)
      _ ≤ _ := by
        rw [abs_mul, abs_neg, abs_of_nonneg hd.le, norm_mul, norm_nearPhaseUnit hd hD,
          one_mul]
        exact add_le_add (add_le_add
          (mul_le_of_le_one_left (abs_nonneg _) hD.le) le_rfl) le_rfl
  have hstrict : |err| < σ * |Z.im| := phase_step_error_lt hd hD hn hL hS hRe' herr
  have hN : 0 < e * normalizedCoefficient d (n + 1) := by
    have herr' : -|err| ≤ e * err := by
      have hneg := neg_le_abs (e * err)
      rw [abs_mul, habsE, one_mul] at hneg
      linarith
    rw [hnext, mul_add, show e * (σ * Z.im) = σ * (e * Z.im) by ring, hIm]
    linarith
  rw [normalizedCoefficient, ← mul_div_assoc, ← mul_left_comm] at hN
  exact (mul_pos_iff_of_pos_left (pow_pos (scale_pos hd) _)).mp
    ((div_pos_iff_of_pos_right (rayLeadingScale_pos hd hD (Nat.succ_pos n))).mp hN)

/-- At an actual old zero lying between two interior phase levels, the
next row has the prescribed strict sign for zero-based rank i. -/
theorem eval_sign_at_oldRoot_in_phaseBand {θ : ℝ} {n i : ℕ} (hn : 150 ≤ n)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hi0 : 0 < i) (hi : i + 1 < rowDegree n)
    (hlo : (i : ℝ) * Real.pi < checkpointPhase n θ)
    (hhi : checkpointPhase n θ < ((i : ℝ) + 1) * Real.pi)
    (hzero : (polynomial n).eval (-modulus θ) = 0) :
    0 < (-1 : ℝ) ^ (i + 1) * (polynomial (n + 1)).eval (-modulus θ) := by
  have hfirst : Real.pi ≤ checkpointPhase n θ := by
    exact ((show Real.pi ≤ (i : ℝ) * Real.pi by
      have h : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by lia)
      simpa using mul_le_mul_of_nonneg_right h Real.pi_pos.le)).trans hlo.le
  have hlast : checkpointPhase n θ ≤ ((((n - 1) / 2 : ℕ) : ℝ) - 1) * Real.pi := by
    have hi' : i + 2 ≤ (n - 1) / 2 := by
      unfold rowDegree at hi
      lia
    have hiR : (i : ℝ) + 2 ≤ (((n - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hi'
    exact hhi.le.trans (mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le)
  have hθ' : θ ∈ Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ.1.le, hθ.2.le⟩
  obtain ⟨hL, hS⟩ := checkpointPhase_interior hn hθ' hfirst hlast
  obtain ⟨hd, hD⟩ := cosine_in_unit hθ
  have hsin : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    have hp : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, hθ.2.le.trans (by linarith [Real.pi_pos])⟩
    rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 by linarith [Real.sin_sq_add_cos_sq θ],
      Real.sqrt_sq hp]
  rw [← hsin] at hS
  simpa only [modulus, neg_sub] using eval_sign_at_oldRoot_of_phaseSign hd hD hn hL hS
    (by simpa only [modulus, neg_sub] using hzero) (nearPhaseUnit_im_sign_between hθ hlo hhi)

end RealRooted.CatalanWordPeaks.CutGeometry
