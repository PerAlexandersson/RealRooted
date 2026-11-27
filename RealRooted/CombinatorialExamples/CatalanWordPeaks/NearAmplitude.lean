/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.FourRays
import RealRooted.CombinatorialExamples.CatalanWordPeaks.RadialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Pointwise near-ray amplitudes and the retained conjugate factor

A single projection comparison controls the reciprocal on the whole ray.
The source's two scale-comparison cases are omitted.

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

open Set Complex MeasureTheory
open scoped ComplexConjugate

private theorem principalRoot_re_pos {u : ℂ} (hu : u ∈ slitPlane) :
    0 < (principalRoot u).re := by
  rw [principalRoot, cpow_inv_two_re, Real.sqrt_pos,
    div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  rcases mem_slitPlane_iff.mp hu with h | h
  · linarith [norm_nonneg u]
  · linarith [abs_re_lt_norm.mpr h, neg_le_abs u.re]

private theorem one_sub_radial_slit {q : ℂ} (hq : q.im ≠ 0 ∨ q.re < 0)
    {t : ℝ} (ht : 0 < t) : 1 - q * (t : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases hq with h | h
  · right
    simpa [sub_im, mul_im] using mul_ne_zero h ht.ne'
  · left
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    linarith [mul_neg_of_neg_of_pos h ht]

/-- The normalized ratio of the same principal cut factor along a positive
radial step. The branch choice forces the ratio to have positive real part. -/
private theorem rootRatio_re_pos {q : ℂ} (hq : q.im ≠ 0 ∨ q.re < 0)
    {t : ℝ} (ht : 0 < t) :
    0 < (principalRoot (1 - q * (t : ℂ)) / principalRoot (1 - q)).re := by
  let g := principalRoot (1 - q * (t : ℂ))
  let h := principalRoot (1 - q)
  have hg : 0 < g.re := principalRoot_re_pos (one_sub_radial_slit hq ht)
  have hh : 0 < h.re := principalRoot_re_pos (by
    simpa using one_sub_radial_slit hq (t := 1) zero_lt_one)
  have hs : 2 * g.re * g.im = -(q.im * t) := by
    have he := congrArg Complex.im (principalRoot_sq (1 - q * (t : ℂ)))
    calc
      _ = g.re * g.im + g.im * g.re := by ring
      _ = _ := by simpa only [g, pow_two, mul_im, sub_im, one_im, ofReal_re,
        ofReal_im, mul_zero, zero_add, zero_sub] using he
  have h₀ : 2 * h.re * h.im = -q.im := by
    have he := congrArg Complex.im (principalRoot_sq (1 - q))
    calc
      _ = h.re * h.im + h.im * h.re := by ring
      _ = _ := by simpa only [h, pow_two, mul_im, sub_im, one_im, zero_sub] using he
  have him : 0 ≤ g.im * h.im := by
    have hprod : 0 ≤ (2 * g.re * (2 * h.re)) * (g.im * h.im) := by
      rw [show (2 * g.re * (2 * h.re)) * (g.im * h.im) =
        (2 * g.re * g.im) * (2 * h.re * h.im) by ring, hs, h₀]
      rw [show -(q.im * t) * -q.im = q.im ^ 2 * t by ring]
      positivity
    exact nonneg_of_mul_nonneg_right hprod (by positivity : 0 < 2 * g.re * (2 * h.re))
  have hne : h ≠ 0 := by
    intro hz
    simp [hz] at hh
  have hnorm := Complex.normSq_pos.mpr hne
  change 0 < (g / h).re
  rw [div_eq_mul_inv, mul_re, inv_re, inv_im, neg_div, mul_neg, sub_neg_eq_add,
    ← mul_div_assoc, ← mul_div_assoc]
  exact add_pos_of_pos_of_nonneg (div_pos (mul_pos hg hh) hnorm) (div_nonneg him hnorm.le)

/-- A principal cut-factor ratio along the outward radial coordinate. -/
def rootRatio (z w : ℂ) (s : ℝ) : ℂ :=
  cutFactor w (z * (1 + (s : ℂ))) / cutFactor w z

private def denominatorCoefficient (d : ℝ) : ℂ :=
  nearPoint d / (nearPoint d - (scale d : ℂ))

private def otherRoots (d : ℝ) (x : ℂ) : ℂ :=
  cutFactor (conj (nearPoint d)) x *
    (cutFactor (farPoint d) x * cutFactor (conj (farPoint d)) x)

private theorem rayPrefactor_near_roots (d : ℝ) (x : ℂ) :
    rayPrefactor d 0 x = -otherRoots d x / (2 * x * ((scale d : ℂ) - x)) := by
  have h : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  rw [rayPrefactor, h, otherRoots]
  simp only [Fin.isValue, cutPoint, Finset.mem_insert, Fin.reduceEq, Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.prod_insert, Fin.coe_ofNat_eq_mod, Nat.one_mod,
    Nat.reduceMod, Finset.prod_singleton, Nat.mod_succ]
  ring

/-- The three regular factors in the near-ray prefactor. -/
theorem rayPrefactor_near_form (d : ℝ) (x : ℂ) :
    rayPrefactor d 0 x =
      -(cutFactor (farPoint d) x * cutFactor (conj (nearPoint d)) x *
        cutFactor (conj (farPoint d)) x) / (2 * x * ((scale d : ℂ) - x)) := by
  rw [rayPrefactor_near_roots, otherRoots]
  ring

/-- The near-ray amplitude normalized at the branch point. -/
def nearAmplitude (d s : ℝ) : ℂ :=
  rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) / rayPrefactor d 0 (nearPoint d)

private def otherRootRatios (d s : ℝ) : ℂ :=
  rootRatio (nearPoint d) (conj (nearPoint d)) s *
    (rootRatio (nearPoint d) (farPoint d) s * rootRatio (nearPoint d) (conj (farPoint d)) s)

private theorem rootRatio_sq_re {z w : ℂ} (hw : w ≠ 0)
    (hq : (z / w).im ≠ 0 ∨ (z / w).re < 0) {s : ℝ} (hs : 0 ≤ s) :
    rootRatio z w s ^ 2 = 1 + z / (z - w) * (s : ℂ) ∧ 0 < (rootRatio z w s).re := by
  have hq₀ : 1 - z / w ∈ slitPlane := by
    simpa using one_sub_radial_slit hq (t := 1) zero_lt_one
  have hne := (mem_slitPlane_iff_arg.mp hq₀).2
  have hwz : z - w ≠ 0 := by
    intro hz
    have hw' : z = w := sub_eq_zero.mp hz
    simp [hw', hw] at hne
  constructor
  · rw [rootRatio, div_pow, cutFactor, cutFactor, principalRoot_sq, principalRoot_sq]
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hwz).symm
    field_simp [hw, hwz, hwz', hne]
    ring
  · have ht : 0 < 1 + s := by positivity
    unfold rootRatio cutFactor
    rw [show z * (1 + (s : ℂ)) / w = z / w * ((1 + s : ℝ) : ℂ) by push_cast; ring]
    exact rootRatio_re_pos hq ht

private theorem near_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) : nearPoint d ≠ 0 := by
  intro h
  simpa [h] using nearPoint_im_pos hd hD

private theorem far_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) : farPoint d ≠ 0 := by
  intro h
  simpa [h] using farPoint_im_pos hd hD

private theorem near_div_conj_near_im {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    0 < (nearPoint d / conj (nearPoint d)).im := by
  have hC : conj (nearPoint d) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 (near_ne_zero hd hD)
  have hnorm := Complex.normSq_pos.mpr hC
  have hRe := nearPoint_re_pos hd
  have hIm := nearPoint_im_pos hd hD
  rw [div_eq_mul_inv, mul_im, inv_re, inv_im, conj_re, conj_im, neg_neg]
  positivity

private theorem near_div_far_im {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    (nearPoint d / farPoint d).im < 0 := by
  have hnorm := Complex.normSq_pos.mpr (far_ne_zero hd hD)
  rw [div_eq_mul_inv, mul_im, inv_re, inv_im]
  exact add_neg
    (mul_neg_of_pos_of_neg (nearPoint_re_pos hd)
      (div_neg_of_neg_of_pos (neg_neg_of_pos (farPoint_im_pos hd hD)) hnorm))
    (mul_neg_of_pos_of_neg (nearPoint_im_pos hd hD)
      (div_neg_of_neg_of_pos (farPoint_re_neg hd) hnorm))

private theorem near_div_conj_far_re {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    (nearPoint d / conj (farPoint d)).re < 0 := by
  have hnorm := Complex.normSq_pos.mpr ((map_ne_zero (starRingEnd ℂ)).2 (far_ne_zero hd hD))
  rw [div_eq_mul_inv, mul_re, inv_re, inv_im, conj_re, conj_im, neg_neg]
  apply sub_neg.mpr
  exact (mul_neg_of_pos_of_neg (nearPoint_re_pos hd)
    (div_neg_of_neg_of_pos (farPoint_re_neg hd) hnorm)).trans
    (mul_pos (nearPoint_im_pos hd hD) (div_pos (farPoint_im_pos hd hD) hnorm))

private theorem cutFactor_ne_of_ratio {z w : ℂ} (hq : (z / w).im ≠ 0 ∨ (z / w).re < 0) :
    cutFactor w z ≠ 0 := by
  have hp : 0 < (cutFactor w z).re := principalRoot_re_pos (by
    simpa using one_sub_radial_slit hq (t := 1) zero_lt_one)
  intro hz
  simp [hz] at hp

private theorem otherRoots_ne {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    otherRoots d (nearPoint d) ≠ 0 := by
  unfold otherRoots
  exact mul_ne_zero (cutFactor_ne_of_ratio (Or.inl (near_div_conj_near_im hd hD).ne'))
    (mul_ne_zero (cutFactor_ne_of_ratio (Or.inl (near_div_far_im hd hD).ne))
      (cutFactor_ne_of_ratio (Or.inr (near_div_conj_far_re hd hD))))

private theorem near_mul_real_im {d t : ℝ} (hd : 0 < d) (hD : d < 1)
    (ht : 0 < t) : 0 < (nearPoint d * (t : ℂ)).im := by
  simpa only [mul_im, ofReal_im, mul_zero, zero_add, ofReal_re] using
    mul_pos (nearPoint_im_pos hd hD) ht

private theorem near_sub_scale_ne {d t : ℝ} (hd : 0 < d) (hD : d < 1) (ht : 0 < t) :
    nearPoint d * (t : ℂ) - (scale d : ℂ) ≠ 0 := by
  have hp := near_mul_real_im hd hD ht
  intro hz
  have h := congrArg Complex.im hz
  simp only [sub_im, ofReal_im, sub_zero, zero_im] at h
  exact hp.ne' h

private theorem nearAmplitude_factorization {d s : ℝ} (hd : 0 < d) (hD : d < 1)
    (hs : 0 ≤ s) :
    nearAmplitude d s = CutBounds.shortReciprocal (denominatorCoefficient d) s *
      otherRootRatios d s := by
  let z := nearPoint d
  let c := (scale d : ℂ)
  let x := z * (1 + (s : ℂ))
  have hz : z ≠ 0 := near_ne_zero hd hD
  have hs' : 0 < 1 + s := by positivity
  have ht : 1 + (s : ℂ) ≠ 0 := by exact_mod_cast hs'.ne'
  have hzc : z - c ≠ 0 := by
    simpa [z, c] using near_sub_scale_ne hd hD (t := 1) zero_lt_one
  have hxc : x - c ≠ 0 := by
    simpa [z, c, x] using near_sub_scale_ne hd hD hs'
  have hden : 1 + denominatorCoefficient d * (s : ℂ) = (x - c) / (z - c) := by
    change 1 + z / (z - c) * (s : ℂ) = (x - c) / (z - c)
    field_simp [hzc]
    simp only [x]
    ring
  have hprod : otherRootRatios d s = otherRoots d x / otherRoots d z := by
    simp only [otherRootRatios, otherRoots, rootRatio, z, x, div_mul_div_comm]
  have hO : otherRoots d z ≠ 0 := otherRoots_ne hd hD
  simp only [nearAmplitude, rayPrefactor_near_roots, CutBounds.shortReciprocal, hden, hprod]
  change (-otherRoots d x / (2 * x * (c - x))) / (-otherRoots d z / (2 * z * (c - z))) =
    (1 + (s : ℂ))⁻¹ * ((x - c) / (z - c))⁻¹ * (otherRoots d x / otherRoots d z)
  have hcz : c - z ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hzc).symm
  have hcx : c - x ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hxc).symm
  have hx : x ≠ 0 := mul_ne_zero hz ht
  field_simp [hO, hx, hz, hzc, hxc, hcz, hcx, ht]
  simp only [x]
  ring

private theorem sine_pos {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    0 < Real.sqrt (1 - d ^ 2) := Real.sqrt_pos.mpr (by nlinarith)

private theorem sine_ge_half {d : ℝ} (hd : 0 < d) (hD : d ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ Real.sqrt (1 - d ^ 2) := by
  apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by nlinarith : 0 ≤ 1 - d ^ 2)]
  nlinarith [mul_nonneg hd.le (show 0 ≤ 1 / 2 - d by linarith)]

private theorem rootRatios_majorants {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) :
    ‖otherRootRatios d s‖ ≤ (1 + s) * (1 + (n : ℝ) * s / 8) ∧
      ‖otherRootRatios d s - 1‖ ≤ ((n : ℝ) / 4 + 2) * s +
        ((n : ℝ) / 4 + 1 / 2) * s ^ 2 := by
  let z := nearPoint d
  let w := farPoint d
  let k := Real.sqrt (1 - d ^ 2)
  have hk : 0 < k := sine_pos hd hD
  have hc : ‖z / (z - conj z)‖ = 1 / (2 * k) := near_conjugate_coefficient hd hD
  have hw : ‖z / (z - w)‖ ≤ 1 / (2 * d) := near_to_far_bound hd hD
  have hh : ‖z / (z - conj w)‖ ≤ 1 := (opposite_cross_bounds hd hD).1
  have hgC := rootRatio_sq_re ((map_ne_zero (starRingEnd ℂ)).2 (near_ne_zero hd hD))
    (Or.inl (near_div_conj_near_im hd hD).ne') hs
  have hgW := rootRatio_sq_re (far_ne_zero hd hD) (Or.inl (near_div_far_im hd hD).ne) hs
  have hgH := rootRatio_sq_re ((map_ne_zero (starRingEnd ℂ)).2 (far_ne_zero hd hD))
    (Or.inr (near_div_conj_far_re hd hD)) hs
  have hlong (k : ℝ) (hk : 0 < k) (h : 2 ≤ (n : ℝ) * k) :
      1 / (2 * k) ≤ (n : ℝ) / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * k)).mpr
    linarith
  have hshort (k : ℝ) (hk : 1 / 2 ≤ k) : 1 / (2 * k) ≤ 1 :=
    (div_le_one (by linarith : 0 < 2 * k)).mpr (by linarith)
  by_cases h : 1 / 2 ≤ d
  · obtain ⟨hm, he⟩ := CutBounds.three_factor_majorants hs (by positivity : 0 ≤ (n : ℝ) / 4)
      (hc.le.trans (hlong k hk hS)) (hw.trans (hshort d h)) hh
      hgC.1 hgW.1 hgH.1 hgC.2.le hgW.2.le hgH.2.le
    exact ⟨hm.trans_eq (by ring), he⟩
  · have hK : 1 / 2 ≤ k := sine_ge_half hd (le_of_not_ge h)
    obtain ⟨hm, he⟩ := CutBounds.three_factor_majorants hs (by positivity : 0 ≤ (n : ℝ) / 4)
      (hw.trans (hlong d hd hL)) (hc.le.trans (hshort k hK)) hh
      hgW.1 hgC.1 hgH.1 hgW.2.le hgC.2.le hgH.2.le
    rw [mul_left_comm (rootRatio _ _ _)] at hm he
    exact ⟨hm.trans_eq (by ring), he⟩

private theorem near_distance_sine {d : ℝ} (hd : 0 < d) (hD : d < 1) (t : ℝ) :
    scale d * Real.sqrt (1 - d ^ 2) ≤ ‖nearPoint d * (t : ℂ) - (scale d : ℂ)‖ := by
  let a := radius d
  let c := scale d
  let k := Real.sqrt (1 - d ^ 2)
  have hk : d ^ 2 + k ^ 2 = 1 := by
    dsimp [k]
    rw [Real.sq_sqrt (by nlinarith : 0 ≤ 1 - d ^ 2)]
    ring
  have hc : 0 < c := scale_pos hd
  have hkn : 0 ≤ k := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (mul_nonneg hc.le hkn) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, sub_im, Complex.mul_re, Complex.mul_im, ofReal_re, ofReal_im,
    mul_zero, sub_zero, zero_add, nearPoint_im_eq hd]
  change (c * k) ^ 2 ≤ (a * d * t - c) * (a * d * t - c) + (a * k * t) * (a * k * t)
  calc
    _ ≤ (a * t - c * d) ^ 2 + (c * k) ^ 2 := le_add_of_nonneg_left (sq_nonneg _)
    _ = (a * d * t - c) ^ 2 + (a * k * t) ^ 2 +
        (c ^ 2 - (a * t) ^ 2) * (d ^ 2 + k ^ 2 - 1) := by ring
    _ = _ := by rw [hk]; ring

private theorem reciprocal_global {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hs : 0 ≤ s) :
    ‖CutBounds.shortReciprocal (denominatorCoefficient d) s‖ ≤
      2 * (n : ℝ) / (1 + s) := by
  let z := nearPoint d
  let c := scale d
  let a := radius d
  let k := Real.sqrt (1 - d ^ 2)
  let x := z * (1 + (s : ℂ))
  have ha : 0 < a := radius_pos hd.le
  have hc : 0 < c := scale_pos hd
  have hk : 0 < k := sine_pos hd hD
  have hs1 : 0 < 1 + s := by positivity
  have hx : x - (c : ℂ) ≠ 0 := by
    simpa [x, z, c] using near_sub_scale_ne hd hD hs1
  have hz : z - (c : ℂ) ≠ 0 := by
    simpa [z, c] using near_sub_scale_ne hd hD (t := 1) zero_lt_one
  have heq : 1 + denominatorCoefficient d * (s : ℂ) =
      (x - (c : ℂ)) / (z - (c : ℂ)) := by
    change 1 + z / (z - (c : ℂ)) * (s : ℂ) = _
    field_simp [hz]
    simp only [x]
    ring
  have hzBound : ‖z - (c : ℂ)‖ ≤ a + c := by
    simpa [sub_eq_add_neg, norm_neg, norm_real, abs_of_pos hc, z, a,
      nearPoint_norm hd hD] using norm_add_le z (-(c : ℂ))
  have hlowC : c * k ≤ ‖x - (c : ℂ)‖ := by
    simpa only [x, z, c, k, ofReal_add, ofReal_one] using
      near_distance_sine hd hD (1 + s)
  have him : (x - (c : ℂ)).im = a * k * (1 + s) := by
    simp [x, z, a, k, Complex.mul_im, nearPoint_im_eq hd]
  have hlowA : a * k ≤ ‖x - (c : ℂ)‖ := by
    calc
      a * k ≤ a * k * (1 + s) := by nlinarith [mul_nonneg (mul_nonneg ha.le hk.le) hs]
      _ = (x - (c : ℂ)).im := him.symm
      _ ≤ _ := Complex.im_le_norm _
  have hratio : ‖z - (c : ℂ)‖ ≤ (n : ℝ) * ‖x - (c : ℂ)‖ := by
    apply (mul_le_mul_iff_left₀ hk).mp
    calc
      _ ≤ (a + c) * k := mul_le_mul_of_nonneg_right hzBound hk.le
      _ ≤ 2 * ‖x - (c : ℂ)‖ := by nlinarith only [hlowA, hlowC]
      _ ≤ ((n : ℝ) * k) * ‖x - (c : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hS (norm_nonneg _)
      _ = _ := by ring
  rw [CutBounds.shortReciprocal, heq, inv_div, norm_mul, norm_inv, norm_div,
    show 1 + (s : ℂ) = ((1 + s : ℝ) : ℂ) by push_cast; rfl,
    norm_real, Real.norm_eq_abs, abs_of_pos hs1, mul_comm, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ hs1.le
  apply (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
  exact hratio.trans (by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (norm_nonneg (x - (c : ℂ)))])

/-- The local error envelope (5) for the actual near-ray amplitude. -/
theorem nearAmplitude_local_error {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) (hs₈ : s ≤ 1 / 8) :
    ‖nearAmplitude d s - 1‖ ≤ (2 * (n : ℝ) / 5 + 9) * s +
      (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2 := by
  rw [nearAmplitude_factorization hd hD hs]
  exact CutBounds.near_local_error hs hs₈ (denominator_near_bound hd hD).le le_rfl
    (rootRatios_majorants hd hD hS hL hs).2

/-- The pointwise bound for the near-ray amplitude on the entire outward ray. -/
theorem nearAmplitude_global {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) : ‖nearAmplitude d s‖ ≤ 2 * (n : ℝ) * (1 + (n : ℝ) * s / 8) := by
  rw [nearAmplitude_factorization hd hD hs, norm_mul]
  calc
    _ ≤ (2 * (n : ℝ) / (1 + s)) * ((1 + s) * (1 + (n : ℝ) * s / 8)) :=
      mul_le_mul (reciprocal_global hd hD hS hs) (rootRatios_majorants hd hD hS hL hs).1
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← mul_assoc, div_mul_cancel₀ _ (by positivity : (1 + s) ≠ 0)]

/-- The global error bound is contained in the common affine envelope of (6). -/
theorem nearAmplitude_tail_error {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) : ‖nearAmplitude d s - 1‖ ≤
      (2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8) := by
  calc
    _ ≤ ‖nearAmplitude d s‖ + 1 := by simpa using norm_sub_le (nearAmplitude d s) 1
    _ ≤ 2 * (n : ℝ) * (1 + (n : ℝ) * s / 8) + 1 :=
      add_le_add (nearAmplitude_global hd hD hS hL hs) le_rfl
    _ ≤ _ := by nlinarith [mul_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n) hs]

/-- The nonzero endpoint by which the near prefactor is normalized. -/
theorem rayPrefactor_near_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    rayPrefactor d 0 (nearPoint d) ≠ 0 := by
  have hnc : nearPoint d - (scale d : ℂ) ≠ 0 := by
    simpa using near_sub_scale_ne hd hD (t := 1) zero_lt_one
  rw [rayPrefactor_near_roots]
  exact div_ne_zero (neg_ne_zero.mpr (otherRoots_ne hd hD))
    (mul_ne_zero (mul_ne_zero (by norm_num) (near_ne_zero hd hD))
      (sub_ne_zero.mpr (sub_ne_zero.mp hnc).symm))

/-- The conjugate-near-point factor retained in the small-angle comparison. -/
def nearConjugateRatio (d s : ℝ) : ℂ :=
  rootRatio (nearPoint d) (conj (nearPoint d)) s

private theorem conjugateRatio_spec {d s : ℝ} (hd : 0 < d) (hD : d < 1) (hs : 0 ≤ s) :
    nearConjugateRatio d s ^ 2 =
      1 + nearPoint d / (nearPoint d - conj (nearPoint d)) * (s : ℂ) ∧
      0 < (nearConjugateRatio d s).re :=
  rootRatio_sq_re ((map_ne_zero (starRingEnd ℂ)).2 (near_ne_zero hd hD))
    (Or.inl (near_div_conj_near_im hd hD).ne') hs

private theorem conjugate_coefficient_re {d : ℝ} (hd : 0 < d) (hD : d < 1) :
    (nearPoint d / (nearPoint d - conj (nearPoint d))).re = 1 / 2 := by
  let z := nearPoint d
  have hne : z - conj z ≠ 0 := by
    intro hz
    have hIm := congrArg Complex.im hz
    change (z - conj z).im = 0 at hIm
    simp only [sub_im, conj_im, sub_neg_eq_add] at hIm
    exact (add_pos (nearPoint_im_pos hd hD) (nearPoint_im_pos hd hD)).ne' hIm
  have hne' : conj z - z ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hne).symm
  have heq : z / (z - conj z) + conj (z / (z - conj z)) = 1 := by
    simp only [map_div₀, map_sub, conj_conj]
    field_simp [hne, hne']
    ring
  have h := congrArg Complex.re heq
  simp only [add_re, conj_re, one_re] at h
  change (z / (z - conj z)).re = _
  linarith

/-- The positive real part of the actual conjugate factor is at least one. -/
theorem nearConjugateRatio_one_le_re {d s : ℝ} (hd : 0 < d) (hD : d < 1) (hs : 0 ≤ s) :
    1 ≤ (nearConjugateRatio d s).re := by
  obtain ⟨hsq, hp⟩ := conjugateRatio_spec hd hD hs
  have h := congrArg Complex.re hsq
  simp only [pow_two, mul_re, add_re, one_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    conjugate_coefficient_re hd hD] at h
  apply (sq_le_sq₀ (by norm_num : 0 ≤ (1 : ℝ)) hp.le).mp
  nlinarith only [h, hs, sq_nonneg (nearConjugateRatio d s).im]

private theorem conjugate_coefficient_le {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    ‖nearPoint d / (nearPoint d - conj (nearPoint d))‖ ≤ (n : ℝ) / 4 := by
  have hk := sine_pos hd hD
  rw [near_conjugate_coefficient hd hD, div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (1 - d ^ 2))]
  linarith

/-- A secant bound for the conjugate factor, using its positive real part. -/
theorem nearConjugateRatio_lipschitz {d s t : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖nearConjugateRatio d s - nearConjugateRatio d t‖ ≤ (n : ℝ) / 8 * |s - t| := by
  let b := nearPoint d / (nearPoint d - conj (nearPoint d))
  let g := nearConjugateRatio d s
  let h := nearConjugateRatio d t
  have hSum : (2 : ℝ) ≤ ‖g + h‖ := by
    have hr : (2 : ℝ) ≤ (g + h).re := by
      rw [add_re]
      exact (by norm_num : (2 : ℝ) = 1 + 1) ▸
        add_le_add (nearConjugateRatio_one_le_re hd hD hs) (nearConjugateRatio_one_le_re hd hD ht)
    exact hr.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have heq : (g - h) * (g + h) = b * ((s : ℂ) - (t : ℂ)) := by
    calc
      _ = g ^ 2 - h ^ 2 := by ring
      _ = _ := by
        rw [(conjugateRatio_spec hd hD hs).1, (conjugateRatio_spec hd hD ht).1]
        dsimp only [b]
        ring
  have hnorm : ‖g - h‖ * ‖g + h‖ = ‖b‖ * |s - t| := by
    simpa only [norm_mul, ← ofReal_sub, norm_real, Real.norm_eq_abs] using congrArg norm heq
  have hbound := mul_le_mul_of_nonneg_right (conjugate_coefficient_le hd hD hS)
    (abs_nonneg (s - t))
  have hstep := mul_le_mul_of_nonneg_left hSum (norm_nonneg (g - h))
  change ‖g - h‖ ≤ _
  linarith

/-- The modulus of the retained conjugate factor on the entire ray. -/
theorem nearConjugateRatio_norm_le {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hs : 0 ≤ s) :
    ‖nearConjugateRatio d s‖ ≤ 1 + (n : ℝ) * s / 8 := by
  have h := CutBounds.factor_norm_bound hs (conjugateRatio_spec hd hD hs).1
  have hmul := mul_le_mul_of_nonneg_right (conjugate_coefficient_le hd hD hS) hs
  linarith

/-- The local loss from the constant term in the broader covariance comparison. -/
theorem nearAmplitude_sixth_error {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d)
    (hs : 0 ≤ s) (hs₆ : s ≤ 1 / 6) :
    ‖nearAmplitude d s - 1‖ ≤ ((n : ℝ) / 2 + 11) * s + ((n : ℝ) / 2 + 1) * s ^ 2 := by
  let R := CutBounds.shortReciprocal (denominatorCoefficient d) s
  let K := otherRootRatios d s
  obtain ⟨hR, hR'⟩ := CutBounds.sixth_reciprocal_bounds hs hs₆ (denominator_near_bound hd hD).le
  have hK := (rootRatios_majorants hd hD hS hL hs).2
  rw [nearAmplitude_factorization hd hD hs]
  change ‖R * K - 1‖ ≤ _
  calc
    _ ≤ ‖R‖ * ‖K - 1‖ + ‖R - 1‖ := by
      rw [← norm_mul, show R * K - 1 = R * (K - 1) + (R - 1) by ring]
      exact norm_add_le _ _
    _ ≤ 2 * (((n : ℝ) / 4 + 2) * s + ((n : ℝ) / 4 + 1 / 2) * s ^ 2) + 7 * s :=
      add_le_add (mul_le_mul hR hK (norm_nonneg _) (by norm_num)) hR'
    _ = _ := by ring

/-- The local loss after retaining the conjugate factor, as in (9). -/
theorem nearAmplitude_conjugate_error {d s : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hdHalf : 1 / 2 ≤ d) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2))
    (hs : 0 ≤ s) (hs₆ : s ≤ 1 / 6) :
    ‖nearAmplitude d s - nearConjugateRatio d s‖ ≤
      11 * s + (1 + 11 * (n : ℝ) / 8) * s ^ 2 + ((n : ℝ) / 8) * s ^ 3 := by
  let z := nearPoint d
  let w := farPoint d
  let g := nearConjugateRatio d s
  let P := rootRatio z w s * rootRatio z (conj w) s
  let R := CutBounds.shortReciprocal (denominatorCoefficient d) s
  have hw : ‖z / (z - w)‖ ≤ 1 := (near_to_far_bound hd hD).trans
    ((div_le_one (by positivity : 0 < 2 * d)).mpr (by linarith))
  have hcw : ‖z / (z - conj w)‖ ≤ 1 := (opposite_cross_bounds hd hD).1
  obtain ⟨hgs, hgr⟩ := rootRatio_sq_re (far_ne_zero hd hD) (Or.inl (near_div_far_im hd hD).ne) hs
  obtain ⟨hhs, hhr⟩ := rootRatio_sq_re ((map_ne_zero (starRingEnd ℂ)).2 (far_ne_zero hd hD))
    (Or.inr (near_div_conj_far_re hd hD)) hs
  have hP : ‖P - 1‖ ≤ 2 * s + s ^ 2 / 2 :=
    (CutBounds.short_product hs hw hcw hgs hhs hgr.le hhr.le).2
  obtain ⟨hR, hR'⟩ := CutBounds.sixth_reciprocal_bounds hs hs₆ (denominator_near_bound hd hD).le
  have hRP : ‖R * P - 1‖ ≤ 11 * s + s ^ 2 := by
    calc
      _ ≤ ‖R‖ * ‖P - 1‖ + ‖R - 1‖ := by
        rw [← norm_mul, show R * P - 1 = R * (P - 1) + (R - 1) by ring]
        exact norm_add_le _ _
      _ ≤ 2 * (2 * s + s ^ 2 / 2) + 7 * s :=
        add_le_add (mul_le_mul hR hP (norm_nonneg _) (by norm_num)) hR'
      _ = _ := by ring
  rw [nearAmplitude_factorization hd hD hs]
  change ‖R * (g * P) - g‖ ≤ _
  rw [show R * (g * P) - g = g * (R * P - 1) by ring, norm_mul]
  calc
    _ ≤ (1 + (n : ℝ) * s / 8) * (11 * s + s ^ 2) :=
      mul_le_mul (nearConjugateRatio_norm_le hd hD hS hs) hRP (norm_nonneg _) (by positivity)
    _ = _ := by ring

end RealRooted.CatalanWordPeaks.CutGeometry
