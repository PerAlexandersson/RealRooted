/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.FourRays
import RealRooted.CombinatorialExamples.CatalanWordPeaks.NearAmplitude
import RealRooted.CombinatorialExamples.CatalanWordPeaks.MomentBounds
public import RealRooted.CombinatorialExamples.CatalanWordPeaks.BetaMoments
import Mathlib.Tactic

/-!
# Far-ray amplitude suppression

The exact radial prefactors are bounded relative to their near endpoints.

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

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Complex MeasureTheory Set
open scoped ComplexConjugate

private theorem norm_cutFactor_sq (z x : ℂ) :
    ‖cutFactor z x‖ ^ 2 = ‖1 - x / z‖ := by
  rw [← norm_pow]
  exact congrArg norm (principalRoot_sq (1 - x / z))

private theorem norm_cutFactor_radial {w z : ℂ} (hz : z ≠ 0) (hwz : w ≠ z)
    {s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) (hb : ‖w / (w - z)‖ ≤ L) :
    ‖cutFactor z (w * (1 + (s : ℂ)))‖ ≤
      ‖cutFactor z w‖ * Real.sqrt (1 + L * s) := by
  have hfactor : 1 - w * (1 + (s : ℂ)) / z =
      (1 - w / z) * (1 + (w / (w - z)) * (s : ℂ)) := by
    field_simp [hz, sub_ne_zero.mpr hwz]
    ring
  have hbound : ‖1 + (w / (w - z)) * (s : ℂ)‖ ≤ 1 + L * s := calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(w / (w - z)) * (s : ℂ)‖ := norm_add_le _ _
    _ = 1 + ‖w / (w - z)‖ * s := by
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ _ := by gcongr
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_cutFactor_sq, hfactor, norm_mul, mul_pow, norm_cutFactor_sq,
    Real.sq_sqrt (by positivity)]
  exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

private theorem sqrt_affine_le {s L : ℝ} (hs : 0 ≤ s) (hL : 0 ≤ L) :
    Real.sqrt (1 + L * s) ≤ 1 + L * s / 2 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (L * s)]

private theorem real_sub_norm_sq (c : ℝ) (z : ℂ) :
    ‖(c : ℂ) - z‖ ^ 2 = c ^ 2 + ‖z‖ ^ 2 - 2 * c * z.re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem real_sub_norm_radial_le {c : ℝ} {z : ℂ} {s : ℝ}
    (hc : 0 ≤ c) (hz : z.re ≤ 0) (hs : 0 ≤ s) :
    ‖(c : ℂ) - z‖ ≤ ‖(c : ℂ) - z * (1 + (s : ℂ))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [real_sub_norm_sq, real_sub_norm_sq, norm_mul,
    show (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hpow : ‖z‖ ^ 2 ≤ (‖z‖ * (1 + s)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (by nlinarith [norm_nonneg z])
  have hre := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc hs) hz
  nlinarith

private theorem rayPrefactor_far_form (d : ℝ) (x : ℂ) :
    rayPrefactor d 1 x =
      -(cutFactor (nearPoint d) x * cutFactor (conj (nearPoint d)) x *
        cutFactor (conj (farPoint d)) x) / (2 * x * ((scale d : ℂ) - x)) := by
  have h : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  rw [rayPrefactor, h]
  simp only [Fin.isValue, cutPoint, Finset.mem_insert, Fin.reduceEq, Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.prod_insert, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Nat.reduceMod, Finset.prod_singleton, Nat.mod_succ]
  ring

/-- The actual upper far-ray prefactor satisfies the affine envelope. -/
private theorem farRay_prefactor_norm_le {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hnd : 2 ≤ (n : ℝ) * d) (hs : 0 ≤ s) :
    ‖rayPrefactor d 1 (farPoint d * (1 + (s : ℂ)))‖ ≤
      ‖rayPrefactor d 1 (farPoint d)‖ * (1 + (1 + (n : ℝ) / 4) * s / 2) := by
  let w := farPoint d
  let z := nearPoint d
  let c : ℂ := (scale d : ℂ)
  let x := w * (1 + (s : ℂ))
  let L : ℝ := 1 + (n : ℝ) / 4
  have hzr : 0 < z.re := nearPoint_re_pos hd
  have hwr : w.re < 0 := farPoint_re_neg hd
  have hwi : 0 < w.im := farPoint_im_pos hd hD
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hzr
  have hw : w ≠ 0 := by
    intro h
    simp [h] at hwr
  have hzc : conj z ≠ 0 := fun h => hz (by simpa using congrArg (fun u : ℂ => conj u) h)
  have hwc : conj w ≠ 0 := fun h => hw (by simpa using congrArg (fun u : ℂ => conj u) h)
  have hwz : w ≠ z := fun h => by rw [h] at hwr; linarith
  have hwzc : w ≠ conj z := fun h => by rw [h, Complex.conj_re] at hwr; linarith
  have hwwc : w ≠ conj w := fun h =>
    by have he := congrArg Complex.im h; rw [Complex.conj_im] at he; linarith
  have hc : 0 < scale d := scale_pos hd
  have hcw : c - w ≠ 0 := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    change scale d = w.re at he
    linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hdirect : ‖w / (w - z)‖ ≤ L := by
    refine (far_to_near_bound hd hD).trans ?_
    change 1 + 1 / (2 * d) ≤ 1 + (n : ℝ) / 4
    apply add_le_add le_rfl
    apply (div_le_iff₀ (by positivity : 0 < 2 * d)).2
    nlinarith
  have hA : ‖cutFactor z x‖ ≤ ‖cutFactor z w‖ * (1 + L * s / 2) :=
    (norm_cutFactor_radial hz hwz hs hL hdirect).trans
      (mul_le_mul_of_nonneg_left (sqrt_affine_le hs hL) (norm_nonneg _))
  have hB : ‖cutFactor (conj z) x‖ ≤ ‖cutFactor (conj z) w‖ * Real.sqrt (1 + s) := by
    simpa only [one_mul] using
      norm_cutFactor_radial hzc hwzc hs zero_le_one (opposite_cross_bounds hd hD).2
  have hC : ‖cutFactor (conj w) x‖ ≤ ‖cutFactor (conj w) w‖ * Real.sqrt (1 + s) := by
    simpa only [one_mul] using norm_cutFactor_radial hwc hwwc hs zero_le_one
      (far_conjugate_bound hd hD)
  have hprod :
      ‖cutFactor z x‖ * ‖cutFactor (conj z) x‖ * ‖cutFactor (conj w) x‖ ≤
        (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
          (1 + L * s / 2) * (1 + s) := calc
    _ ≤ (‖cutFactor z w‖ * (1 + L * s / 2)) *
          (‖cutFactor (conj z) w‖ * Real.sqrt (1 + s)) *
          (‖cutFactor (conj w) w‖ * Real.sqrt (1 + s)) := by gcongr
    _ = (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
        (1 + L * s / 2) * Real.sqrt (1 + s) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have hx : ‖x‖ = ‖w‖ * (1 + s) := by
    rw [show x = w * ((1 + s : ℝ) : ℂ) by dsimp [x]; push_cast; rfl, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hdist : ‖c - w‖ ≤ ‖c - x‖ := real_sub_norm_radial_le hc.le hwr.le hs
  have hden : 0 < 2 * ‖w‖ * ‖c - w‖ :=
    mul_pos (mul_pos (by norm_num) (norm_pos_iff.mpr hw)) (norm_pos_iff.mpr hcw)
  have hden' : 0 < 2 * ‖x‖ * ‖c - x‖ := by
    rw [hx]
    exact mul_pos (mul_pos (by norm_num)
      (mul_pos (norm_pos_iff.mpr hw) (by positivity))) ((norm_pos_iff.mpr hcw).trans_le hdist)
  change ‖rayPrefactor d 1 x‖ ≤ ‖rayPrefactor d 1 w‖ * (1 + L * s / 2)
  simp only [rayPrefactor_far_form, norm_div, norm_neg, norm_mul, Complex.norm_two]
  calc
    _ ≤ (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
        (1 + L * s / 2) * (1 + s) / (2 * ‖x‖ * ‖c - x‖) :=
      div_le_div_of_nonneg_right hprod hden'.le
    _ ≤ (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) *
        (1 + L * s / 2) * (1 + s) / (2 * ‖x‖ * ‖c - w‖) := by
      apply div_le_div_of_nonneg_left (by positivity) _ (by gcongr)
      rw [hx]
      positivity
    _ = _ := by
      change _ = (‖cutFactor z w‖ * ‖cutFactor (conj z) w‖ * ‖cutFactor (conj w) w‖) /
        (2 * ‖w‖ * ‖c - w‖) * (1 + L * s / 2)
      rw [hx]
      field_simp [(norm_pos_iff.mpr hw).ne', (norm_pos_iff.mpr hcw).ne',
        (show 1 + s ≠ 0 by positivity)]

private theorem rayPrefactor_conjFar_form (d : ℝ) (x : ℂ) :
    rayPrefactor d 2 x =
      -(cutFactor (conj (nearPoint d)) x * cutFactor (nearPoint d) x *
        cutFactor (farPoint d) x) / (2 * x * ((scale d : ℂ) - x)) := by
  have h : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
  rw [rayPrefactor, h]
  simp only [Fin.isValue, cutPoint, Finset.mem_insert, zero_ne_one, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true, Finset.prod_insert, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Nat.one_mod, Finset.prod_singleton, Nat.mod_succ]
  ring

private theorem norm_cutFactor_conj (z x : ℂ) :
    ‖cutFactor (conj z) (conj x)‖ = ‖cutFactor z x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_cutFactor_sq, norm_cutFactor_sq,
    show 1 - conj x / conj z = conj (1 - x / z) by simp,
    Complex.norm_conj]

private theorem norm_rayPrefactor_conjFar (d : ℝ) (x : ℂ) :
    ‖rayPrefactor d 2 (conj x)‖ = ‖rayPrefactor d 1 x‖ := by
  have h₁ := norm_cutFactor_conj (nearPoint d) x
  have h₂ := norm_cutFactor_conj (conj (nearPoint d)) x
  have h₃ := norm_cutFactor_conj (conj (farPoint d)) x
  rw [Complex.conj_conj] at h₂ h₃
  have hdist : ‖(scale d : ℂ) - conj x‖ = ‖(scale d : ℂ) - x‖ := by
    rw [show (scale d : ℂ) - conj x = conj ((scale d : ℂ) - x) by simp,
      Complex.norm_conj]
  simp only [rayPrefactor_conjFar_form, rayPrefactor_far_form, norm_div, norm_neg,
    norm_mul, h₁, h₂, h₃, hdist, Complex.norm_conj]

private theorem norm_rayIntegrand {d : ℝ} {n : ℕ} {j : Fin 4} {s : ℝ} (hs : 0 ≤ s) :
    ‖rayIntegrand d n j s‖ = BetaMoments.rayWeight n s *
      ‖rayPrefactor d j (cutPoint d j * (1 + (s : ℂ)))‖ := by
  rw [rayIntegrand, BetaMoments.rayWeight, norm_mul, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    show (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    inv_pow, div_eq_mul_inv]

/-- Each actual far-ray integral is bounded by the upper far endpoint times
six fifths of the mass of the radial density. -/
private theorem farRay_integral_norm_le {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 2 ≤ (n : ℝ) * d) (j : Fin 4) (hj : j = 1 ∨ j = 2) :
    ‖∫ s in Ioi (0 : ℝ), rayIntegrand d n j s‖ ≤
      (6 / 5 : ℝ) * BetaMoments.mass n * ‖rayPrefactor d 1 (farPoint d)‖ := by
  have hn0 : 0 < n := by lia
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let A := ‖rayPrefactor d 1 (farPoint d)‖
  let B : ℝ := (1 + (n : ℝ) / 4) / 2
  obtain ⟨henv, hmoment⟩ := BetaMoments.affine_moment (n := n) (by linarith) A (A * B)
  have hmon : ∀ s ∈ Ioi (0 : ℝ), ‖rayIntegrand d n j s‖ ≤
      (A + A * B * s) * BetaMoments.rayWeight n s := by
    intro s hs
    have hs0 : 0 < s := hs
    have hnorm : ‖rayPrefactor d j (cutPoint d j * (1 + (s : ℂ)))‖ =
        ‖rayPrefactor d 1 (farPoint d * (1 + (s : ℂ)))‖ := by
      obtain rfl | rfl := hj
      · rfl
      · change ‖rayPrefactor d 2 (conj (farPoint d) * (1 + (s : ℂ)))‖ = _
        rw [show conj (farPoint d) * (1 + (s : ℂ)) =
          conj (farPoint d * (1 + (s : ℂ))) by simp, norm_rayPrefactor_conjFar]
    rw [norm_rayIntegrand hs0.le, hnorm]
    calc
      _ ≤ BetaMoments.rayWeight n s * (A * (1 + (1 + (n : ℝ) / 4) * s / 2)) :=
        mul_le_mul_of_nonneg_left (farRay_prefactor_norm_le hd hD hnd hs0.le)
          (BetaMoments.rayWeight_nonneg n hs0.le)
      _ = _ := by dsimp [B]; ring
  calc
    _ ≤ ∫ s in Ioi (0 : ℝ), ‖rayIntegrand d n j s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi (0 : ℝ), (A + A * B * s) * BetaMoments.rayWeight n s :=
      setIntegral_mono_on (rayIntegrand_integrable hd hD hn0 j).norm henv measurableSet_Ioi hmon
    _ = BetaMoments.mass n * (A + A * B * BetaMoments.moment n 1) := hmoment
    _ = BetaMoments.mass n * A * (1 + B * BetaMoments.moment n 1) := by ring
    _ ≤ _ := by
      have hnum : 1 + B * BetaMoments.moment n 1 ≤ (6 / 5 : ℝ) := by
        rw [BetaMoments.moment_one (by linarith)]
        dsimp [B]
        have hp : 0 < (n : ℝ) - 3 / 2 := by linarith
        have hfrac : ((1 + (n : ℝ) / 4) / 2) * (3 / 2) / ((n : ℝ) - 3 / 2) ≤ 1 / 5 :=
          (div_le_iff₀ hp).2 (by linarith)
        rw [← mul_div_assoc]
        linarith
      rw [show (6 / 5 : ℝ) * BetaMoments.mass n * A =
        BetaMoments.mass n * A * (6 / 5) by ring]
      exact mul_le_mul_of_nonneg_left hnum
        (mul_nonneg (BetaMoments.mass_pos hn0).le (norm_nonneg _))

private theorem norm_cutFactor_sq_distance {z x : ℂ} (hz : z ≠ 0) :
    ‖cutFactor z x‖ ^ 2 = ‖x - z‖ / ‖z‖ := by
  rw [norm_cutFactor_sq, show 1 - x / z = (z - x) / z by field_simp,
    norm_div, norm_sub_rev]

private theorem norm_sub_conj_swap (z w : ℂ) : ‖w - conj z‖ = ‖z - conj w‖ := by
  calc
    _ = ‖conj (w - conj z)‖ := (Complex.norm_conj _).symm
    _ = ‖conj w - z‖ := by simp only [map_sub, Complex.conj_conj]
    _ = _ := norm_sub_rev _ _

private theorem endpoint_dist_le {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    ‖(scale d : ℂ) - nearPoint d‖ ≤ ‖(scale d : ℂ) - farPoint d‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [real_sub_norm_sq, real_sub_norm_sq]
  have hnorm := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_order hd hD).le
  have hnear := mul_pos (scale_pos hd) (nearPoint_re_pos hd)
  have hfar := mul_neg_of_pos_of_neg (scale_pos hd) (farPoint_re_neg hd)
  linarith

/-- The actual far endpoint amplitude is bounded by the near endpoint
amplitude divided by the square root of the near point's sine. -/
private theorem farRay_endpoint_bound {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    ‖rayPrefactor d 1 (farPoint d)‖ * Real.sqrt (Real.sqrt (1 - d ^ 2)) ≤
      ‖rayPrefactor d 0 (nearPoint d)‖ := by
  let z := nearPoint d
  let w := farPoint d
  let c : ℂ := (scale d : ℂ)
  let σ := Real.sqrt (1 - d ^ 2)
  let τ := w.im / ‖w‖
  let P := ‖w - z‖ * ‖w - conj z‖ * 2
  have hz : 0 < ‖z‖ := by rw [show ‖z‖ = radius d from nearPoint_norm hd hD]; exact radius_pos hd.le
  have hw : 0 < ‖w‖ := by
    rw [show ‖w‖ = (radius d)⁻¹ from farPoint_norm hd hD]
    exact inv_pos.mpr (radius_pos hd.le)
  have hz' := norm_pos_iff.mp hz
  have hw' := norm_pos_iff.mp hw
  have hzc' : conj z ≠ 0 := fun h => hz' (by simpa using congrArg (fun u : ℂ => conj u) h)
  have hwc' : conj w ≠ 0 := fun h => hw' (by simpa using congrArg (fun u : ℂ => conj u) h)
  have hcz : 0 < ‖c - z‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he := congrArg Complex.im (sub_eq_zero.mp h)
    change 0 = z.im at he
    linarith [nearPoint_im_pos hd hD]
  have hdist : ‖c - z‖ ≤ ‖c - w‖ := endpoint_dist_le hd hD
  have hcw := hcz.trans_le hdist
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hτ : τ ≤ 1 := (div_le_one hw).2 (Complex.im_le_norm _)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have him : z.im = ‖z‖ * σ := by
    rw [show ‖z‖ = radius d from nearPoint_norm hd hD]
    exact nearPoint_im_eq hd
  have hnear : ‖rayPrefactor d 0 z‖ ^ 2 =
      P * σ / (2 * ‖z‖ * ‖w‖ * ‖c - z‖) ^ 2 := by
    simp only [rayPrefactor_near_form, norm_div, norm_neg, norm_mul, Complex.norm_two,
      div_pow, mul_pow]
    change ‖cutFactor w z‖ ^ 2 * ‖cutFactor (conj z) z‖ ^ 2 * ‖cutFactor (conj w) z‖ ^ 2 /
      (2 ^ 2 * ‖z‖ ^ 2 * ‖c - z‖ ^ 2) = P * σ / (2 ^ 2 * ‖z‖ ^ 2 * ‖w‖ ^ 2 * ‖c - z‖ ^ 2)
    rw [norm_cutFactor_sq_distance hw', norm_cutFactor_sq_distance hzc',
      norm_cutFactor_sq_distance hwc', norm_sub_conjugate z (nearPoint_im_pos hd hD).le, him,
      norm_sub_rev z w, ← norm_sub_conj_swap z w]
    simp only [Complex.norm_conj, P]
    field_simp [hz.ne', hw.ne', hcz.ne']
  have hfar : ‖rayPrefactor d 1 w‖ ^ 2 =
      P * τ / (2 * ‖z‖ * ‖w‖ * ‖c - w‖) ^ 2 := by
    simp only [rayPrefactor_far_form, norm_div, norm_neg, norm_mul, Complex.norm_two,
      div_pow, mul_pow]
    change ‖cutFactor z w‖ ^ 2 * ‖cutFactor (conj z) w‖ ^ 2 * ‖cutFactor (conj w) w‖ ^ 2 /
      (2 ^ 2 * ‖w‖ ^ 2 * ‖c - w‖ ^ 2) = P * τ / (2 ^ 2 * ‖z‖ ^ 2 * ‖w‖ ^ 2 * ‖c - w‖ ^ 2)
    rw [norm_cutFactor_sq_distance hz', norm_cutFactor_sq_distance hzc',
      norm_cutFactor_sq_distance hwc', norm_sub_conjugate w (farPoint_im_pos hd hD).le]
    simp only [Complex.norm_conj, P, τ]
    field_simp [hz.ne', hw.ne', hcw.ne']
  change ‖rayPrefactor d 1 w‖ * Real.sqrt σ ≤ ‖rayPrefactor d 0 z‖
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hσ, hfar, hnear]
  calc
    _ = P * (τ * σ) / (2 * ‖z‖ * ‖w‖ * ‖c - w‖) ^ 2 := by ring
    _ ≤ P * σ / (2 * ‖z‖ * ‖w‖ * ‖c - w‖) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hτ hσ
      rw [one_mul] at h
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hP) (sq_nonneg _)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (mul_nonneg hP hσ) (by positivity)
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      exact mul_le_mul_of_nonneg_left hdist (by positivity)

private theorem radius_sq_pow_eq {d : ℝ} (hd : 0 ≤ d) (n : ℕ) :
    (radius d ^ 2) ^ n = ((1 + 2 * d) ^ n)⁻¹ := by
  have hp : 0 < 1 + 2 * d := by positivity
  rw [show radius d ^ 2 = (1 + 2 * d)⁻¹ by
    rw [← one_div]
    exact (eq_div_iff hp.ne').2 (radius_relation hd), inv_pow]

private theorem forty_lt_radial_power {d : ℝ} {n : ℕ} (hd : 0 < d)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d) :
    (40 : ℝ) < (1 + 2 * d) ^ n := by
  let k := n / 6
  have hk : 6 * k ≤ n := by dsimp [k]; lia
  have hk' : 4 * n ≤ 25 * k := by dsimp [k]; lia
  have hkc : (4 : ℝ) * (n : ℝ) ≤ 25 * (k : ℝ) := by exact_mod_cast hk'
  have hbase : (241 / 125 : ℝ) ≤ 1 + (k : ℝ) * (2 * d) := by
    nlinarith [mul_le_mul_of_nonneg_right hkc hd.le]
  calc
    _ < (241 / 125 : ℝ) ^ 6 := by norm_num
    _ ≤ (1 + (k : ℝ) * (2 * d)) ^ 6 := pow_le_pow_left₀ (by norm_num) hbase 6
    _ ≤ ((1 + 2 * d) ^ k) ^ 6 :=
      pow_le_pow_left₀ (by positivity) (one_add_mul_le_pow (by linarith : -2 ≤ 2 * d) k) 6
    _ = (1 + 2 * d) ^ (6 * k) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hk

private theorem fast_exp_bound {n : ℕ} (hn : 150 ≤ n) :
    120 * (n : ℝ) ^ 2 < (2 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [pow_succ (2 : ℝ) n, Nat.cast_succ]
    have h : 120 * ((n : ℝ) + 1) ^ 2 ≤ 2 * (120 * (n : ℝ) ^ 2) := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    linarith

/-- Exponential suppression for the small-angle range, in the units of the
leading near-ray amplitude. -/
private theorem farRay_smallAngle_factor_lt {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hdAngle : (1 / 2 : ℝ) ≤ d)
    (hnsin : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    (6 / 5 : ℝ) * (radius d ^ 2) ^ n / Real.sqrt (Real.sqrt (1 - d ^ 2)) <
      1 / (100 * (n : ℝ)) := by
  let σ := Real.sqrt (1 - d ^ 2)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by lia)
  have hσ : 0 < σ := Real.sqrt_pos.2 (by nlinarith)
  have hσ1 : σ ≤ 1 := by
    apply (sq_le_sq₀ hσ.le zero_le_one).mp
    dsimp [σ]
    rw [Real.sq_sqrt (by nlinarith)]
    nlinarith
  have hσ' : σ ≤ Real.sqrt σ := by
    apply (sq_le_sq₀ hσ.le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hσ.le, pow_two]
    exact mul_le_of_le_one_right hσ.le hσ1
  have hsqrt : 1 ≤ (n : ℝ) * Real.sqrt σ := by
    have hp := mul_le_mul_of_nonneg_left hσ' hnR.le
    change 2 ≤ (n : ℝ) * σ at hnsin
    linarith
  have hradial : (radius d ^ 2) ^ n ≤ ((2 : ℝ) ^ n)⁻¹ := by
    rw [radius_sq_pow_eq hd.le]
    have hp : (2 : ℝ) ^ n ≤ (1 + 2 * d) ^ n :=
      pow_le_pow_left₀ (by norm_num) (by linarith) n
    simpa only [one_div] using (one_div_le_one_div_of_le (by positivity) hp)
  change (6 / 5 : ℝ) * (radius d ^ 2) ^ n / Real.sqrt σ < _
  calc
    _ ≤ (6 / 5 : ℝ) * (((2 : ℝ) ^ n)⁻¹) / Real.sqrt σ := by gcongr
    _ ≤ (6 / 5 : ℝ) * (((2 : ℝ) ^ n)⁻¹) * (n : ℝ) := by
      apply (div_le_iff₀ (Real.sqrt_pos.2 hσ)).2
      nlinarith [mul_le_mul_of_nonneg_left hsqrt
        (show 0 ≤ (6 / 5 : ℝ) * (((2 : ℝ) ^ n)⁻¹) by positivity)]
    _ < _ := by
      have hp : 0 < (2 : ℝ) ^ n := by positivity
      have h := fast_exp_bound hn
      rw [show (6 / 5 : ℝ) * ((2 : ℝ) ^ n)⁻¹ * (n : ℝ) =
        ((6 / 5 : ℝ) * (n : ℝ)) / ((2 : ℝ) ^ n) by rw [div_eq_mul_inv]; ring]
      apply (div_lt_div_iff₀ hp (by positivity : 0 < 100 * (n : ℝ))).2
      nlinarith

/-- Exponential suppression for the complementary range. The sixth power of
a rational Bernoulli bound gives the needed estimate without logarithms. -/
private theorem farRay_largeAngle_factor_lt {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d)
    (hσ : (7 / 10 : ℝ) ≤ Real.sqrt (1 - d ^ 2)) :
    (6 / 5 : ℝ) * (radius d ^ 2) ^ n / Real.sqrt (Real.sqrt (1 - d ^ 2)) <
      1 / 25 := by
  let σ := Real.sqrt (1 - d ^ 2)
  have hσ0 : 0 < σ := (by norm_num : (0 : ℝ) < 7 / 10).trans_le hσ
  have hroot : (5 / 6 : ℝ) ≤ Real.sqrt σ := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hσ0.le]
    change (7 / 10 : ℝ) ≤ σ at hσ
    linarith
  have hradial : (radius d ^ 2) ^ n < 1 / 40 := by
    rw [radius_sq_pow_eq hd.le, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) (forty_lt_radial_power hd hn hnd)
  change (6 / 5 : ℝ) * (radius d ^ 2) ^ n / Real.sqrt σ < _
  calc
    _ ≤ (6 / 5 : ℝ) * (radius d ^ 2) ^ n / (5 / 6 : ℝ) := by gcongr
    _ < _ := by linarith

/-- The signed summand of the exact coefficient formula at the specified cut. -/
def rayCoefficientTerm (d : ℝ) (n : ℕ) (j : Fin 4) : ℂ :=
  (-((cutPoint d j)⁻¹ ^ n) / (Real.pi : ℂ)) * ∫ s in Ioi (0 : ℝ), rayIntegrand d n j s

/-- The leading amplitude used to normalize the scaled Catalan coefficient. -/
def rayLeadingScale (d : ℝ) (n : ℕ) : ℝ :=
  (2 / Real.pi) * (radius d)⁻¹ ^ n * BetaMoments.mass n *
    ‖rayPrefactor d 0 (nearPoint d)‖

/-- The leading near-ray scale is strictly positive at every positive size. -/
theorem rayLeadingScale_pos {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1) (hn : 0 < n) :
    0 < rayLeadingScale d n := by
  unfold rayLeadingScale
  exact mul_pos (mul_pos (mul_pos (by positivity) (pow_pos (inv_pos.mpr (radius_pos hd.le)) _))
    (BetaMoments.mass_pos hn)) (norm_pos_iff.mpr (rayPrefactor_near_ne_zero hd hD))

/-- The normalized real contribution of the two far-ray terms. -/
def farRayError (d : ℝ) (n : ℕ) : ℝ :=
  (rayCoefficientTerm d n 1 + rayCoefficientTerm d n 2).re / rayLeadingScale d n

private theorem farRay_coefficientTerm_norm_le {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 2 ≤ (n : ℝ) * d) (j : Fin 4) (hj : j = 1 ∨ j = 2) :
    ‖rayCoefficientTerm d n j‖ ≤
      radius d ^ n / Real.pi *
        ((6 / 5 : ℝ) * BetaMoments.mass n * ‖rayPrefactor d 1 (farPoint d)‖) := by
  have hr : ‖cutPoint d j‖ = (radius d)⁻¹ := by
    obtain rfl | rfl := hj
    · exact farPoint_norm hd hD
    · change ‖conj (farPoint d)‖ = _
      rw [Complex.norm_conj, farPoint_norm hd hD]
  rw [rayCoefficientTerm, norm_mul, norm_div, norm_neg, norm_pow, norm_inv, hr, inv_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left (farRay_integral_norm_le hd hD hn hnd j hj)
    (div_nonneg (pow_nonneg (radius_pos hd.le).le _) Real.pi_pos.le)

/-- The bound for the actual normalized far-ray contribution in the coefficient
identity. The weight is the radial separation of the near and far endpoints. -/
private theorem farRayError_abs_le {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 2 ≤ (n : ℝ) * d) :
    |farRayError d n| ≤
      (6 / 5 : ℝ) * (radius d ^ 2) ^ n / Real.sqrt (Real.sqrt (1 - d ^ 2)) := by
  let h := Real.sqrt (Real.sqrt (1 - d ^ 2))
  have hp : 0 < h := Real.sqrt_pos.2 (Real.sqrt_pos.2 (by nlinarith))
  have hn0 : 0 < n := by lia
  have hm := BetaMoments.mass_pos hn0
  have hr := radius_pos hd.le
  have hb : ‖rayPrefactor d 1 (farPoint d)‖ ≤ ‖rayPrefactor d 0 (nearPoint d)‖ / h :=
    (le_div_iff₀ hp).2 (farRay_endpoint_bound hd hD)
  rw [farRayError, abs_div, abs_of_pos (rayLeadingScale_pos hd hD hn0)]
  apply (div_le_iff₀ (rayLeadingScale_pos hd hD hn0)).2
  calc
    _ ≤ ‖rayCoefficientTerm d n 1 + rayCoefficientTerm d n 2‖ := Complex.abs_re_le_norm _
    _ ≤ ‖rayCoefficientTerm d n 1‖ + ‖rayCoefficientTerm d n 2‖ := norm_add_le _ _
    _ ≤ 2 * (radius d ^ n / Real.pi *
        ((6 / 5 : ℝ) * BetaMoments.mass n * ‖rayPrefactor d 1 (farPoint d)‖)) := by
      rw [two_mul]
      exact add_le_add (farRay_coefficientTerm_norm_le hd hD hn hnd 1 (.inl rfl))
        (farRay_coefficientTerm_norm_le hd hD hn hnd 2 (.inr rfl))
    _ ≤ 2 * (radius d ^ n / Real.pi *
        ((6 / 5 : ℝ) * BetaMoments.mass n * (‖rayPrefactor d 0 (nearPoint d)‖ / h))) := by
      gcongr
    _ = _ := by
      change _ = (6 / 5 : ℝ) * (radius d ^ 2) ^ n / h * rayLeadingScale d n
      rw [rayLeadingScale, pow_right_comm (radius d) 2 n, inv_pow, pow_two]
      field_simp [hp.ne', Real.pi_ne_zero, (pow_pos hr n).ne']

/-- On the small-angle range the actual far-ray contribution is less than
one hundredth of the inverse row length, in the leading amplitude units. -/
theorem farRayError_smallAngle {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hdAngle : (1 / 2 : ℝ) ≤ d)
    (hnsin : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    |farRayError d n| < 1 / (100 * (n : ℝ)) := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnd : 2 ≤ (n : ℝ) * d := by nlinarith
  exact (farRayError_abs_le hd hD hn hnd).trans_lt
    (farRay_smallAngle_factor_lt hd hD hn hdAngle hnsin)

/-- On the large-angle range the actual far-ray contribution is less than
one twenty-fifth of the leading amplitude. -/
theorem farRayError_largeAngle {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d)
    (hσ : (7 / 10 : ℝ) ≤ Real.sqrt (1 - d ^ 2)) :
    |farRayError d n| < 1 / 25 :=
  (farRayError_abs_le hd hD hn (by linarith)).trans_lt
    (farRay_largeAngle_factor_lt hd hD hn hnd hσ)

/-- The uniform bound under the interior radial premises. -/
theorem farRayError_interior {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d)
    (hnsin : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    |farRayError d n| < 1 / 25 := by
  by_cases h : (1 / 2 : ℝ) ≤ d
  · refine (farRayError_smallAngle hd hD hn h hnsin).trans_le ?_
    have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  · have hσ : (7 / 10 : ℝ) ≤ Real.sqrt (1 - d ^ 2) := by
      apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (by nlinarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) hd.le]
    exact farRayError_largeAngle hd hD hn hnd hσ

end RealRooted.CatalanWordPeaks.CutGeometry
