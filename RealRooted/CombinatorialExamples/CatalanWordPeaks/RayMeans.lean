/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.NearAmplitude
public import RealRooted.CombinatorialExamples.CatalanWordPeaks.FarRays
public import RealRooted.CombinatorialExamples.CatalanWordPeaks.RadialBounds
import RealRooted.CombinatorialExamples.CatalanWordPeaks.MomentBounds
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-!
# Near-ray means and real coefficient normalization

We integrate the pointwise amplitude bounds and combine conjugate rays.
The centered step identity is proved directly, without an intermediate covariance definition.

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

private def weightedNear (d : ℝ) (n : ℕ) (s : ℝ) : ℂ :=
  (BetaMoments.rayWeight n s : ℂ) * nearAmplitude d s

/-- The normalized mean `J_n` of the actual near-ray amplitude. -/
def nearMean (d : ℝ) (n : ℕ) : ℂ :=
  (∫ s in Ioi (0 : ℝ), (BetaMoments.rayWeight n s : ℂ) * nearAmplitude d s) /
    (BetaMoments.mass n : ℂ)

private theorem nearMean_eq_weighted (d : ℝ) (n : ℕ) :
    nearMean d n = (∫ s in Ioi (0 : ℝ), weightedNear d n s) / (BetaMoments.mass n : ℂ) :=
  rfl

private theorem rayIntegrand_near_eq {d : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (s : ℝ) :
    rayIntegrand d n 0 s = rayPrefactor d 0 (nearPoint d) * weightedNear d n s := by
  rw [rayIntegrand]
  change (Real.sqrt s : ℂ) * (1 + (s : ℂ))⁻¹ ^ (n + 1) *
      rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) = _
  simp only [weightedNear, BetaMoments.rayWeight, ofReal_pow, ofReal_add, ofReal_one,
    nearAmplitude, inv_pow, div_eq_mul_inv, ofReal_mul, ofReal_inv]
  rw [show rayPrefactor d 0 (nearPoint d) *
      ((Real.sqrt s : ℂ) * ((1 + (s : ℂ)) ^ (n + 1))⁻¹ *
        (rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) *
          (rayPrefactor d 0 (nearPoint d))⁻¹)) =
      (Real.sqrt s : ℂ) * ((1 + (s : ℂ)) ^ (n + 1))⁻¹ *
        rayPrefactor d 0 (nearPoint d * (1 + (s : ℂ))) *
        (rayPrefactor d 0 (nearPoint d) * (rayPrefactor d 0 (nearPoint d))⁻¹) by ring,
    mul_inv_cancel₀ (rayPrefactor_near_ne_zero hd hD), mul_one]

private theorem weightedNear_integrable {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) : IntegrableOn (weightedNear d n) (Ioi 0) := by
  have h := (rayIntegrand_integrable hd hD hn 0).congr_fun
    (fun s _ => rayIntegrand_near_eq hd hD n s) measurableSet_Ioi
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (rayPrefactor_near_ne_zero hd hD)) _).mp h

/-- The near ray integral factors exactly into its endpoint, normalization,
and the mean of the amplitude whose error is estimated below. -/
private theorem nearRay_integral_eq_mean {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1) (hn : 0 < n) :
    (∫ s in Ioi (0 : ℝ), rayIntegrand d n 0 s) =
      rayPrefactor d 0 (nearPoint d) * (BetaMoments.mass n : ℂ) * nearMean d n := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => rayIntegrand_near_eq hd hD n s),
    integral_const_mul, nearMean_eq_weighted]
  have hb : (BetaMoments.mass n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (BetaMoments.mass_pos hn).ne'
  rw [mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hb]

private theorem rayWeight_integrable {n : ℕ} (hn : 0 < n) :
    IntegrableOn (BetaMoments.rayWeight n) (Ioi 0) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : (((0 : ℕ) : ℝ)) + 1 / 2 < (n : ℝ) := by norm_num; linarith
  simpa using BetaMoments.integrableOn_moment h

private theorem norm_weightedNear_sub_weight {d : ℝ} {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ‖weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)‖ =
      ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s := by
  rw [weightedNear, show (BetaMoments.rayWeight n s : ℂ) * nearAmplitude d s -
      (BetaMoments.rayWeight n s : ℂ) =
    (BetaMoments.rayWeight n s : ℂ) * (nearAmplitude d s - 1) by ring,
    norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (BetaMoments.rayWeight_nonneg n hs),
    mul_comm]

private theorem weightedNear_loss_integrable {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) :
    IntegrableOn (fun s => ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s) (Ioi 0) := by
  have hw : IntegrableOn (fun s => (BetaMoments.rayWeight n s : ℂ)) (Ioi 0) :=
    (rayWeight_integrable hn).ofReal
  have h : IntegrableOn (fun s => ‖weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)‖)
      (Ioi 0) := ((weightedNear_integrable hd hD hn).sub hw).norm
  exact h.congr_fun (fun _ hs => norm_weightedNear_sub_weight hs.le) measurableSet_Ioi

private theorem nearMean_norm_sub_one_le {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) :
    ‖nearMean d n - 1‖ ≤
      (∫ s in Ioi (0 : ℝ), ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s) /
        BetaMoments.mass n := by
  have hpos := BetaMoments.mass_pos hn
  have hmass : (BetaMoments.mass n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  have hcast : (∫ s in Ioi (0 : ℝ), (BetaMoments.rayWeight n s : ℂ)) =
      (BetaMoments.mass n : ℂ) := integral_complex_ofReal
  have hw : IntegrableOn (fun s => (BetaMoments.rayWeight n s : ℂ)) (Ioi 0) :=
    (rayWeight_integrable hn).ofReal
  have hi := weightedNear_integrable hd hD hn
  rw [nearMean_eq_weighted]
  rw [div_sub_one hmass]
  have hdiff : (∫ s in Ioi (0 : ℝ), weightedNear d n s) - (BetaMoments.mass n : ℂ) =
      ∫ s in Ioi (0 : ℝ), (weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)) := by
    rw [integral_sub hi hw, hcast]
  rw [hdiff, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  apply div_le_div_of_nonneg_right _ hpos.le
  have h := norm_integral_le_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun s => weightedNear d n s - (BetaMoments.rayWeight n s : ℂ))
  have heq :
      (∫ s in Ioi (0 : ℝ), ‖weightedNear d n s - (BetaMoments.rayWeight n s : ℂ)‖) =
        ∫ s in Ioi (0 : ℝ), ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s :=
    setIntegral_congr_fun measurableSet_Ioi (fun _ hs => norm_weightedNear_sub_weight hs.le)
  exact h.trans_eq heq

private theorem near_loss_integral_bound {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d) :
    (∫ s in Ioi (0 : ℝ), ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s) /
      BetaMoments.mass n < 73 / 100 := by
  let M := BetaMoments.mass n
  let L : Set ℝ := Ioc 0 (1 / 8)
  let T : Set ℝ := Ioi (1 / 8)
  let f (s : ℝ) := ‖nearAmplitude d s - 1‖ * BetaMoments.rayWeight n s
  let g (s : ℝ) := ((2 * (n : ℝ) / 5 + 9) * s +
    (2 * (n : ℝ) / 5 + 4 / 5) * s ^ 2) * BetaMoments.rayWeight n s
  let h (s : ℝ) := ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) * BetaMoments.rayWeight n s
  have hnN : 0 < n := by lia
  have hM : 0 < M := BetaMoments.mass_pos hnN
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hR : 0 ≤ (1 / 8 : ℝ) := by norm_num
  have hf : IntegrableOn f (Ioi 0) := weightedNear_loss_integrable hd hD hnN
  have hfL : IntegrableOn f L := hf.mono_set Ioc_subset_Ioi_self
  have hfT : IntegrableOn f T := hf.mono_set (Ioi_subset_Ioi hR)
  have hLocalData := BetaMoments.near_local_integral_bound hn
  have hg : IntegrableOn g L := hLocalData.1
  have hhFull := (BetaMoments.affine_moment (n := n) (by linarith)
    (2 * (n : ℝ) + 1) ((2 * (n : ℝ) + 1) * (n : ℝ) / 8)).1
  have hh : IntegrableOn h T :=
    (hhFull.mono_set (Ioi_subset_Ioi hR)).congr_fun (fun s _ => by dsimp [h]; ring)
      measurableSet_Ioi
  have hcmpLocal : ∀ s ∈ L, f s ≤ g s := by
    intro s hs
    change s ∈ Ioc 0 (1 / 8) at hs
    exact mul_le_mul_of_nonneg_right (nearAmplitude_local_error hd hD hS hL hs.1.le hs.2)
      (BetaMoments.rayWeight_nonneg n hs.1.le)
  have hcmpTail : ∀ s ∈ T, f s ≤ h s := by
    intro s hs
    have hs0 : 0 ≤ s := hR.trans (mem_Ioi.mp hs).le
    exact mul_le_mul_of_nonneg_right (nearAmplitude_tail_error hd hD hS hL hs0)
      (BetaMoments.rayWeight_nonneg n hs0)
  have hLocalLe : (∫ s in L, f s) ≤ ∫ s in L, g s :=
    setIntegral_mono_on hfL hg measurableSet_Ioc hcmpLocal
  have hTailLe : (∫ s in T, f s) ≤ ∫ s in T, h s :=
    setIntegral_mono_on hfT hh measurableSet_Ioi hcmpTail
  have hLocal : (∫ s in L, f s) / M < 71 / 100 :=
    (div_le_div_of_nonneg_right hLocalLe hM.le).trans_lt hLocalData.2
  have hTail : (∫ s in T, f s) / M < 1 / 50 :=
    (div_le_div_of_nonneg_right hTailLe hM.le).trans_lt (BetaMoments.near_tail_integral_bound hn)
  have hdisj : Disjoint L T := Set.disjoint_left.mpr fun _ hs ht => (not_lt_of_ge hs.2) ht
  have hunion : L ∪ T = Ioi 0 := Ioc_union_Ioi_eq_Ioi hR
  have hsplit : (∫ s in Ioi (0 : ℝ), f s) = (∫ s in L, f s) + ∫ s in T, f s := by
    calc
      _ = ∫ s in L ∪ T, f s := by rw [hunion]
      _ = _ := setIntegral_union hdisj measurableSet_Ioi hfL hfT
  change (∫ s in Ioi (0 : ℝ), f s) / M < _
  rw [hsplit, add_div]
  exact (add_lt_add hLocal hTail).trans_le (by norm_num)

/-- The checked near-ray mean lies within `73/100` of one in the interior
range where both radial endpoint distances have the indicated lower bounds. -/
theorem nearMean_close_to_one {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d) :
    ‖nearMean d n - 1‖ < 73 / 100 :=
  (nearMean_norm_sub_one_le hd hD (by lia)).trans_lt (near_loss_integral_bound hd hD hn hS hL)

/-- Centering the amplitude at any constant gives the exact successive-size difference. -/
theorem nearMean_step_centered {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) (a : ℂ) :
    nearMean d (n + 1) - nearMean d n =
      -(∫ s in Ioi (0 : ℝ),
        ((BetaMoments.tiltAverage n * BetaMoments.rayWeight n s -
          BetaMoments.rayWeight (n + 1) s : ℝ) : ℂ) * (nearAmplitude d s - a)) /
        ((BetaMoments.mass n * BetaMoments.tiltAverage n : ℝ) : ℂ) := by
  let η : ℂ := (BetaMoments.tiltAverage n : ℂ)
  let w (m : ℕ) (s : ℝ) : ℂ := (BetaMoments.rayWeight m s : ℂ)
  have hw0 : IntegrableOn (w n) (Ioi 0) := (rayWeight_integrable hn).ofReal
  have hw1 : IntegrableOn (w (n + 1)) (Ioi 0) :=
    (rayWeight_integrable (Nat.succ_pos n)).ofReal
  have h0 := weightedNear_integrable hd hD hn
  have h1 : IntegrableOn (weightedNear d (n + 1)) (Ioi 0) :=
    weightedNear_integrable hd hD (by lia)
  have hw := (hw0.const_mul η).sub hw1
  have hg := (h0.const_mul η).sub h1
  have hz : (∫ s in Ioi (0 : ℝ), η * w n s - w (n + 1) s) = 0 := by
    rw [integral_sub (hw0.const_mul η) hw1, integral_const_mul]
    simp only [w, integral_complex_ofReal]
    rw [← BetaMoments.mass, ← BetaMoments.mass, BetaMoments.mass_succ hn, ofReal_mul]
    exact sub_self _
  have heq (s : ℝ) :
      ((BetaMoments.tiltAverage n * BetaMoments.rayWeight n s -
        BetaMoments.rayWeight (n + 1) s : ℝ) : ℂ) * (nearAmplitude d s - a) =
      (η * weightedNear d n s - weightedNear d (n + 1) s) -
        a * (η * w n s - w (n + 1) s) := by
    simp only [η, w, weightedNear, ofReal_sub, ofReal_mul]
    ring
  have hInt : (∫ s in Ioi (0 : ℝ),
      ((BetaMoments.tiltAverage n * BetaMoments.rayWeight n s -
        BetaMoments.rayWeight (n + 1) s : ℝ) : ℂ) * (nearAmplitude d s - a)) =
      η * (∫ s in Ioi (0 : ℝ), weightedNear d n s) -
        ∫ s in Ioi (0 : ℝ), weightedNear d (n + 1) s := by
    have hs := integral_sub hg (hw.const_mul a)
    simp only [Pi.sub_apply] at hs
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => heq s),
      hs, integral_const_mul, hz, mul_zero, sub_zero,
      integral_sub (h0.const_mul η) h1, integral_const_mul]
  have hη : η ≠ 0 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact ofReal_ne_zero.mpr (ne_of_gt (div_pos (by linarith) (by positivity)))
  have hM : (BetaMoments.mass n : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (BetaMoments.mass_pos hn).ne'
  rw [nearMean_eq_weighted, nearMean_eq_weighted]
  rw [hInt, BetaMoments.mass_succ hn]
  simp only [ofReal_mul]
  change _ / (η * (BetaMoments.mass n : ℂ)) - _ / (BetaMoments.mass n : ℂ) =
    -_ / ((BetaMoments.mass n : ℂ) * η)
  field_simp [hη, hM]
  ring

/-- The near amplitude is integrable against the radial weight at each positive size. -/
theorem nearAmplitude_weighted_integrable {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 0 < n) :
    IntegrableOn (fun s => (BetaMoments.rayWeight n s : ℂ) * nearAmplitude d s) (Ioi 0) :=
  weightedNear_integrable hd hD hn

private theorem cutPoint_rev (d : ℝ) (j : Fin 4) : cutPoint d j.rev = conj (cutPoint d j) := by
  fin_cases j <;> simp [cutPoint, Fin.rev]

private theorem cutPoint_pos_scale_ne {d a b : ℝ} (hd : 0 < d) (hD : d < 1)
    {i j : Fin 4} (hij : i ≠ j) (ha : 0 < a) (hb : 0 < b) :
    cutPoint d j * (a : ℂ) ≠ cutPoint d i * (b : ℂ) := by
  intro he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at hre him
  have hs (r : ℝ) (hr : 0 < r) :
      0 < (nearPoint d).re * r ∧ (farPoint d).re * r < 0 ∧
      0 < (nearPoint d).im * r ∧ 0 < (farPoint d).im * r :=
    ⟨mul_pos (nearPoint_re_pos hd) hr, mul_neg_of_neg_of_pos (farPoint_re_neg hd) hr,
      mul_pos (nearPoint_im_pos hd hD) hr, mul_pos (farPoint_im_pos hd hD) hr⟩
  obtain ⟨ha₁, ha₂, ha₃, ha₄⟩ := hs a ha
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hs b hb
  fin_cases i <;> fin_cases j <;>
    simp only [cutPoint, Complex.conj_re, Complex.conj_im, neg_mul] at hre him <;>
    first | exact hij rfl | linarith

private theorem cutPoint_ne_zero {d : ℝ} (hd : 0 < d) (hD : d < 1) (i : Fin 4) :
    cutPoint d i ≠ 0 := by
  exact norm_pos_iff.mp (cutPoint_norm_pos hd hD i)

private theorem cutFactor_argument_ne_pi {d t : ℝ} (hd : 0 < d) (hD : d < 1)
    {i j : Fin 4} (hij : i ≠ j) (ht : 0 < t) :
    (1 - (cutPoint d j * (t : ℂ)) / cutPoint d i).arg ≠ Real.pi := by
  let q := (cutPoint d j * (t : ℂ)) / cutPoint d i
  intro ha
  change (1 - q).arg = Real.pi at ha
  obtain ⟨hr, hi⟩ := Complex.arg_eq_pi_iff.1 ha
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hr hi
  have hq : q = (q.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      linarith
  have he := (div_eq_iff (cutPoint_ne_zero hd hD i)).mp hq
  exact cutPoint_pos_scale_ne hd hD hij ht (show 0 < q.re by linarith)
    (by simpa only [mul_comm] using he)

private theorem cutFactor_conj {z x : ℂ} (h : (1 - x / z).arg ≠ Real.pi) :
    cutFactor (conj z) (conj x) = conj (cutFactor z x) := by
  simp only [cutFactor, principalRoot]
  rw [show 1 - conj x / conj z = conj (1 - x / z) by simp, Complex.conj_cpow _ _ h]
  rw [map_inv₀, map_ofNat]

private theorem rayPrefactor_rev {d t : ℝ} (hd : 0 < d) (hD : d < 1)
    (j : Fin 4) (ht : 0 < t) :
    rayPrefactor d j.rev (conj (cutPoint d j * (t : ℂ))) =
      conj (rayPrefactor d j (cutPoint d j * (t : ℂ))) := by
  let x := cutPoint d j * (t : ℂ)
  have hmem {i k : Fin 4} (hi : i ∈ Finset.univ.erase k) :
      i.rev ∈ Finset.univ.erase k.rev :=
    Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hi).1 (Fin.rev_injective h),
      Finset.mem_univ _⟩
  have hprod :
      (∏ i ∈ Finset.univ.erase j, conj (cutFactor (cutPoint d i) x)) =
      ∏ i ∈ Finset.univ.erase j.rev, cutFactor (cutPoint d i) (conj x) := by
    refine Finset.prod_bij' (fun i _ => i.rev) (fun i _ => i.rev)
      (fun i hi => hmem hi) (fun i hi => by simpa using hmem hi)
      (fun i _ => Fin.rev_rev i) (fun i _ => Fin.rev_rev i) ?_
    intro i hi
    rw [cutPoint_rev]
    exact (cutFactor_conj (cutFactor_argument_ne_pi hd hD (Finset.mem_erase.mp hi).1 ht)).symm
  change rayPrefactor d j.rev (conj x) = conj (rayPrefactor d j x)
  simp only [rayPrefactor, map_div₀, map_neg, map_mul, map_sub, map_ofNat, Complex.conj_ofReal,
    map_prod, hprod]

private theorem rayIntegrand_rev {d s : ℝ} (hd : 0 < d) (hD : d < 1)
    (n : ℕ) (j : Fin 4) (hs : 0 < s) :
    rayIntegrand d n j.rev s = conj (rayIntegrand d n j s) := by
  have h := rayPrefactor_rev hd hD j (show 0 < 1 + s by positivity)
  rw [Complex.ofReal_add, Complex.ofReal_one] at h
  simp only [map_mul, map_add, map_one, Complex.conj_ofReal, ← cutPoint_rev d j] at h
  simp only [rayIntegrand, map_mul, map_pow, map_inv₀, map_add, map_one, Complex.conj_ofReal]
  rw [h]

/-- The coefficient terms from opposite cuts are exact complex conjugates. -/
private theorem rayCoefficientTerm_rev {d : ℝ} (hd : 0 < d) (hD : d < 1) (n : ℕ) (j : Fin 4) :
    rayCoefficientTerm d n j.rev = conj (rayCoefficientTerm d n j) := by
  rw [rayCoefficientTerm, rayCoefficientTerm,
    setIntegral_congr_fun measurableSet_Ioi (fun _ hs => rayIntegrand_rev hd hD n j hs),
    integral_conj, cutPoint_rev]
  simp

/-- The unit-modulus phase factor carried by the upper near ray. -/
noncomputable def nearPhaseUnit (d : ℝ) (n : ℕ) : ℂ :=
  -(nearPoint d)⁻¹ ^ n * rayPrefactor d 0 (nearPoint d) /
    (((radius d)⁻¹ ^ n * ‖rayPrefactor d 0 (nearPoint d)‖ : ℝ) : ℂ)

/-- The normalized near-ray phase factor lies on the unit circle. -/
theorem norm_nearPhaseUnit {d : ℝ} (hd : 0 < d) (hD : d < 1) (n : ℕ) :
    ‖nearPhaseUnit d n‖ = 1 := by
  have h : 0 < (radius d)⁻¹ ^ n * ‖rayPrefactor d 0 (nearPoint d)‖ :=
    mul_pos (pow_pos (inv_pos.2 (radius_pos hd.le)) _)
      (norm_pos_iff.mpr (rayPrefactor_near_ne_zero hd hD))
  rw [nearPhaseUnit, norm_div, norm_mul, norm_neg, norm_pow, norm_inv,
    nearPoint_norm hd hD, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h, div_self h.ne']

/-- The actual polynomial value in the units of the leading near amplitude. -/
noncomputable def normalizedCoefficient (d : ℝ) (n : ℕ) : ℝ :=
  scale d ^ n * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) / rayLeadingScale d n

private theorem nearCoefficientTerm_normalization {d : ℝ} {n : ℕ} (hd : 0 < d)
    (hD : d < 1) (hn : 0 < n) :
    2 * (rayCoefficientTerm d n 0).re / rayLeadingScale d n =
      (nearPhaseUnit d n * nearMean d n).re := by
  let A := (radius d)⁻¹ ^ n * ‖rayPrefactor d 0 (nearPoint d)‖
  have hA : 0 < A := mul_pos (pow_pos (inv_pos.2 (radius_pos hd.le)) _)
    (norm_pos_iff.mpr (rayPrefactor_near_ne_zero hd hD))
  have hscale : rayLeadingScale d n = (2 / Real.pi) * BetaMoments.mass n * A := by
    dsimp [rayLeadingScale, A]
    ring
  have hreal : (2 : ℂ) * rayCoefficientTerm d n 0 =
      (rayLeadingScale d n : ℂ) * (nearPhaseUnit d n * nearMean d n) := by
    rw [rayCoefficientTerm, nearRay_integral_eq_mean hd hD hn, nearPhaseUnit, hscale]
    change (2 : ℂ) * ((-((nearPoint d)⁻¹ ^ n) / (Real.pi : ℂ)) * _) =
      (((2 / Real.pi) * BetaMoments.mass n * A : ℝ) : ℂ) *
        (-(nearPoint d)⁻¹ ^ n * rayPrefactor d 0 (nearPoint d) / (A : ℂ) * nearMean d n)
    push_cast
    calc
      _ = ((2 : ℂ) * ((-((nearPoint d)⁻¹ ^ n) / (Real.pi : ℂ)) *
          (rayPrefactor d 0 (nearPoint d) * (BetaMoments.mass n : ℂ) * nearMean d n))) *
          ((A : ℂ) * (A : ℂ)⁻¹) := by
        rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hA.ne'), mul_one]
      _ = _ := by ring
  have hre := congrArg Complex.re hreal
  have hre2 : (2 : ℂ).re = 2 := by norm_num
  have him2 : (2 : ℂ).im = 0 := by norm_num
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre2, him2,
    zero_mul, sub_zero] at hre
  apply (div_eq_iff (rayLeadingScale_pos hd hD hn).ne').2
  simpa only [Complex.mul_re, mul_comm] using hre

/-- The exact normalized coefficient as a near-ray mean and a real far-ray error. -/
theorem normalizedCoefficient_eq_near_add_far {d : ℝ} {n : ℕ} (hd : 0 < d)
    (hD : d < 1) (hn : 0 < n) :
    normalizedCoefficient d n = (nearPhaseUnit d n * nearMean d n).re + farRayError d n := by
  have h := analyticGenerating_fourRays hd hD hn
  change _ = ∑ j : Fin 4, rayCoefficientTerm d n j at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  have hr := congrArg Complex.re h
  change scale d ^ n * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) =
      (rayCoefficientTerm d n 0 + (rayCoefficientTerm d n 1 +
        (rayCoefficientTerm d n 2 + rayCoefficientTerm d n 3))).re at hr
  have hconj : rayCoefficientTerm d n 3 = conj (rayCoefficientTerm d n 0) :=
    rayCoefficientTerm_rev hd hD n 0
  rw [hconj] at hr
  have hp : scale d ^ n * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) =
      2 * (rayCoefficientTerm d n 0).re +
      (rayCoefficientTerm d n 1 + rayCoefficientTerm d n 2).re := by
    simp only [Complex.add_re, Complex.conj_re] at hr ⊢
    linarith
  rw [normalizedCoefficient, hp, add_div, nearCoefficientTerm_normalization hd hD hn, farRayError]

/-- In the interior band the actual normalized value is within 77/100 of
the real part of its leading phase. -/
private theorem normalizedCoefficient_close_to_phase {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d)
    (hsin : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    |normalizedCoefficient d n - (nearPhaseUnit d n).re| < 77 / 100 := by
  have hn0 : 0 < n := by lia
  have hnr := nearMean_close_to_one hd hD hn hsin (by linarith : 2 ≤ (n : ℝ) * d)
  have hfar := farRayError_interior hd hD hn hnd hsin
  have hne :
      |(nearPhaseUnit d n * nearMean d n).re - (nearPhaseUnit d n).re| < 73 / 100 := by
    rw [← Complex.sub_re, show nearPhaseUnit d n * nearMean d n - nearPhaseUnit d n =
      nearPhaseUnit d n * (nearMean d n - 1) by ring]
    exact (Complex.abs_re_le_norm _).trans_lt (by
      simpa only [norm_mul, norm_nearPhaseUnit hd hD n, one_mul] using hnr)
  rw [normalizedCoefficient_eq_near_add_far hd hD hn0,
    show (nearPhaseUnit d n * nearMean d n).re + farRayError d n - (nearPhaseUnit d n).re =
      ((nearPhaseUnit d n * nearMean d n).re - (nearPhaseUnit d n).re) + farRayError d n by ring]
  exact (abs_add_le _ _).trans_lt (by linarith)

/-- The original polynomial has the alternating sign at each phase level
where the quantitative interior premises hold. -/
theorem eval_sign_of_nearPhaseUnit {d : ℝ} {n k : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hnd : 29 / 10 ≤ (n : ℝ) * d)
    (hsin : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2))
    (hphase : (nearPhaseUnit d n).re = (-1 : ℝ) ^ k) :
    0 < (-1 : ℝ) ^ k * (polynomial n).eval (1 - (scale d ^ 2)⁻¹) := by
  have hn0 : 0 < n := by lia
  have hb := normalizedCoefficient_close_to_phase hd hD hn hnd hsin
  rw [hphase] at hb
  let e := (-1 : ℝ) ^ k
  have he : |e| = 1 := by simp [e, abs_pow]
  have he2 : e ^ 2 = 1 := by dsimp [e]; rw [pow_right_comm]; norm_num
  have he' : |e * (normalizedCoefficient d n - e)| < 77 / 100 := by
    rw [abs_mul, he, one_mul]
    exact hb
  have hY : 0 < e * normalizedCoefficient d n := by
    have hm := (abs_lt.mp he').1
    rw [mul_sub, ← pow_two, he2] at hm
    linarith
  rw [normalizedCoefficient, ← mul_div_assoc, ← mul_left_comm] at hY
  exact (pos_of_mul_pos_right
    ((div_pos_iff_of_pos_right (rayLeadingScale_pos hd hD hn0)).mp hY)
    (pow_nonneg (scale_pos hd).le _))

end RealRooted.CatalanWordPeaks.CutGeometry
