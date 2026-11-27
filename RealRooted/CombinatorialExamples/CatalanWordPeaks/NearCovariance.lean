/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.RayMeans
import RealRooted.CombinatorialExamples.CatalanWordPeaks.MomentBounds
import Mathlib.Tactic

/-!
# Successive-size bounds for the near mean

The signed density is centered at its change of sign. Its first moment and
the common affine tail control the successive-size difference.

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

open MeasureTheory Set Complex
open scoped NNReal

namespace RealRooted.CatalanWordPeaks.CutGeometry

open BetaMoments

private def weighted (n : ℕ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  (rayWeight n s : ℂ) * f s

private def signedWeight (n : ℕ) (s : ℝ) : ℝ :=
  tiltAverage n * rayWeight n s - rayWeight (n + 1) s

private def signedIntegrand (n : ℕ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  (signedWeight n s : ℂ) * f s

private theorem signedWeight_eq (n : ℕ) (s : ℝ) :
    signedWeight n s = (tiltAverage n - (1 + s)⁻¹) * rayWeight n s := by
  have h := rayWeight_shift (Nat.le_succ n) s
  rw [show n.succ - n = 1 by lia, pow_one] at h
  unfold signedWeight
  rw [h]
  ring

private theorem signed_integrable {n : ℕ} {f : ℝ → ℂ}
    (h₀ : IntegrableOn (weighted n f) (Ioi 0)) (h₁ : IntegrableOn (weighted (n + 1) f) (Ioi 0)) :
    IntegrableOn (signedIntegrand n f) (Ioi 0) := by
  apply IntegrableOn.congr_fun ((h₀.const_mul (tiltAverage n : ℂ)).sub h₁) _ measurableSet_Ioi
  intro s _
  dsimp only [signedIntegrand, signedWeight, weighted, Pi.sub_apply]
  push_cast
  ring

private theorem weighted_const_integrable {n : ℕ} (hn : 0 < n) (a : ℂ) :
    IntegrableOn (weighted n (fun _ => a)) (Ioi 0) := by
  have h : (0 : ℝ) + 1 / 2 < (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hw : IntegrableOn (rayWeight n) (Ioi 0) := by
    simpa using integrableOn_moment (n := n) (j := 0) (by simpa using h)
  exact hw.ofReal.mul_const a

private theorem weighted_sub {n : ℕ} {f g : ℝ → ℂ}
    (hf : IntegrableOn (weighted n f) (Ioi 0)) (hg : IntegrableOn (weighted n g) (Ioi 0)) :
    IntegrableOn (weighted n (fun s => f s - g s)) (Ioi 0) := by
  apply IntegrableOn.congr_fun (hf.sub hg) _ measurableSet_Ioi
  intro s _
  simp only [Pi.sub_apply, weighted, mul_sub]

private theorem nearMean_step_signed {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 0 < n) (a : ℂ) :
    nearMean d (n + 1) - nearMean d n =
      -(∫ s in Ioi (0 : ℝ), signedIntegrand n (fun s => nearAmplitude d s - a) s) /
        ((mass n * tiltAverage n : ℝ) : ℂ) := by
  simpa only [signedIntegrand, signedWeight] using nearMean_step_centered hd hD hn a

private theorem tiltAverage_pos {n : ℕ} (hn : 150 ≤ n) : 0 < tiltAverage n :=
  lt_of_lt_of_le (by norm_num) (tiltAverage_ge hn)

private theorem tiltAverage_le_one (n : ℕ) : tiltAverage n ≤ 1 := by
  unfold tiltAverage
  apply (div_le_one (by positivity)).mpr
  linarith

private theorem centered_tilt_bounds {n : ℕ} (hn : 150 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    |tiltAverage n - (1 + s)⁻¹| ≤ 1 ∧
      |tiltAverage n - (1 + s)⁻¹| ≤ s + 3 / (2 * (n : ℝ)) := by
  have hq := tiltAverage_pos hn
  have hq₁ := tiltAverage_le_one n
  have hu : 0 ≤ (1 + s)⁻¹ := by positivity
  have hu₁ : (1 + s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hs' : 1 - (1 + s)⁻¹ ≤ s := by
    have heq : 1 - (1 + s)⁻¹ = s / (1 + s) := by
      field_simp [show 1 + s ≠ 0 by positivity]
      ring
    rw [heq]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : 1 - tiltAverage n ≤ 3 / (2 * (n : ℝ)) := by
    have heq : 1 - tiltAverage n = 3 / (2 * ((n : ℝ) + 1)) := by
      unfold tiltAverage
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

private theorem norm_signedIntegrand {n : ℕ} {f : ℝ → ℂ} {s : ℝ} (hs : 0 ≤ s) :
    ‖signedIntegrand n f s‖ = ‖f s‖ * |tiltAverage n - (1 + s)⁻¹| * rayWeight n s := by
  rw [signedIntegrand, signedWeight_eq, norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (rayWeight_nonneg n hs)]
  ring

private def momentEnvelope (n j : ℕ) (s : ℝ) : ℝ :=
  s ^ j * (s + 3 / (2 * (n : ℝ))) * rayWeight n s

private theorem momentEnvelope_data {n j : ℕ} (hn : 150 ≤ n) (hj : j ≤ 3) :
    IntegrableOn (momentEnvelope n j) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), momentEnvelope n j s) = mass n * tiltedMoment n j := by
  let e : ℝ := 3 / (2 * (n : ℝ))
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ 3 := by exact_mod_cast hj
  have h0 := integrableOn_moment (n := n) (j := j) (by linarith)
  have h1 := integrableOn_moment (n := n) (j := j + 1) (by push_cast; linarith)
  have hEq (s : ℝ) : momentEnvelope n j s =
      s ^ (j + 1) * rayWeight n s + e * (s ^ j * rayWeight n s) := by
    simp only [momentEnvelope, pow_succ, e]
    ring
  have hmass := mass_pos (n := n) (by lia)
  constructor
  · exact IntegrableOn.congr_fun (h1.add (h0.const_mul e))
      (fun s _ => (hEq s).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hEq s),
      integral_add h1 (h0.const_mul e), integral_const_mul, ← rawMoment, ← rawMoment]
    unfold tiltedMoment moment
    dsimp [e]
    field_simp [hmass.ne']

private theorem piecewise_upper_bound {f p q : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hp : IntegrableOn p (Ioi 0))
    (hq : IntegrableOn q (Ioi (1 / 6)))
    (hp0 : ∀ s : ℝ, 0 < s → 0 ≤ p s)
    (hlocal : ∀ s ∈ Ioc 0 (1 / 6), f s ≤ p s)
    (htail : ∀ s ∈ Ioi (1 / 6), f s ≤ q s) :
    (∫ s in Ioi (0 : ℝ), f s) ≤
      (∫ s in Ioi (0 : ℝ), p s) + ∫ s in Ioi (1 / 6 : ℝ), q s := by
  let L : Set ℝ := Ioc 0 (1 / 6)
  let T : Set ℝ := Ioi (1 / 6)
  have hr : 0 ≤ (1 / 6 : ℝ) := by norm_num
  have hfL := hf.mono_set (show L ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  have hfT := hf.mono_set (show T ⊆ Ioi 0 from Ioi_subset_Ioi hr)
  calc
    _ = ∫ s in L ∪ T, f s := by rw [show L ∪ T = Ioi 0 from Ioc_union_Ioi_eq_Ioi hr]
    _ = (∫ s in L, f s) + ∫ s in T, f s :=
      setIntegral_union (Set.disjoint_left.mpr fun _ hs ht => (not_lt_of_ge hs.2) ht)
        measurableSet_Ioi hfL hfT
    _ ≤ (∫ s in L, p s) + ∫ s in T, q s := add_le_add
      (setIntegral_mono_on hfL (hp.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hlocal)
      (setIntegral_mono_on hfT hq measurableSet_Ioi htail)
    _ ≤ _ := add_le_add (setIntegral_mono_set hp
      (Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioi) hp0)
      (Filter.Eventually.of_forall Ioc_subset_Ioi_self)) le_rfl

private def affineTail (n : ℕ) (s : ℝ) : ℝ :=
  ((2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) * rayWeight n s

private theorem affineTail_integrable {n : ℕ} (hn : 150 ≤ n) :
    IntegrableOn (affineTail n) (Ioi (1 / 6)) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hfull := (affine_moment (n := n) (by linarith)
    (2 * (n : ℝ) + 1) ((2 * (n : ℝ) + 1) * (n : ℝ) / 8)).1
  exact (hfull.mono_set (Ioi_subset_Ioi (by norm_num))).congr_fun
    (fun s _ => by unfold affineTail; ring) measurableSet_Ioi

private theorem signed_integral_envelope {n : ℕ} (hn : 150 ≤ n) {f : ℝ → ℂ}
    (hf : IntegrableOn (signedIntegrand n f) (Ioi 0)) {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hlocal : ∀ s ∈ Ioc 0 (1 / 6), ‖f s‖ ≤ A * s + B * s ^ 2 + C * s ^ 3)
    (htail : ∀ s ∈ Ioi (1 / 6), ‖f s‖ ≤ (2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8)) :
    ‖∫ s in Ioi (0 : ℝ), signedIntegrand n f s‖ / mass n <
      A * tiltedMoment n 1 + B * tiltedMoment n 2 + C * tiltedMoment n 3 + 1 / (20 * (n : ℝ)) := by
  let g := fun s => ‖signedIntegrand n f s‖
  let p := fun s => A * momentEnvelope n 1 s + B * momentEnvelope n 2 s + C * momentEnvelope n 3 s
  have hmass := mass_pos (n := n) (by lia)
  have hthreshold : 0 ≤ (1 / 6 : ℝ) := by norm_num
  obtain ⟨h1, h1i⟩ := momentEnvelope_data (j := 1) hn (by decide)
  obtain ⟨h2, h2i⟩ := momentEnvelope_data (j := 2) hn (by decide)
  obtain ⟨h3, h3i⟩ := momentEnvelope_data (j := 3) hn (by decide)
  have hp : IntegrableOn p (Ioi 0) :=
    ((h1.const_mul A).add (h2.const_mul B)).add (h3.const_mul C)
  have hpInt : (∫ s in Ioi (0 : ℝ), p s) / mass n =
      A * tiltedMoment n 1 + B * tiltedMoment n 2 + C * tiltedMoment n 3 := by
    have h12 : IntegrableOn
        (fun s => A * momentEnvelope n 1 s + B * momentEnvelope n 2 s) (Ioi 0) :=
      (h1.const_mul A).add (h2.const_mul B)
    change (∫ s in Ioi (0 : ℝ),
      (fun t => A * momentEnvelope n 1 t + B * momentEnvelope n 2 t) s +
      C * momentEnvelope n 3 s) / mass n = _
    rw [integral_add h12 (h3.const_mul C), integral_add (h1.const_mul A) (h2.const_mul B),
      integral_const_mul, integral_const_mul, integral_const_mul, h1i, h2i, h3i]
    field_simp [hmass.ne']
  have hg : IntegrableOn g (Ioi 0) := hf.norm
  have hp0 (s : ℝ) (hs : 0 < s) : 0 ≤ p s := by
    have hw := rayWeight_nonneg n hs.le
    simp only [p, momentEnvelope]
    positivity
  have hloc (s : ℝ) (hs : s ∈ Ioc 0 (1 / 6)) : g s ≤ p s := by
    dsimp only [g]
    rw [norm_signedIntegrand hs.1.le]
    calc
      _ ≤ (A * s + B * s ^ 2 + C * s ^ 3) * (s + 3 / (2 * (n : ℝ))) * rayWeight n s :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hlocal s hs) (centered_tilt_bounds hn hs.1.le).2
          (abs_nonneg _) (by have := hs.1; positivity)) (rayWeight_nonneg n hs.1.le)
      _ = p s := by simp only [p, momentEnvelope, pow_one]; ring
  have htail' : ∀ s ∈ Ioi (1 / 6), g s ≤ affineTail n s := by
    intro s hs
    have hs0 : 0 ≤ s := hthreshold.trans hs.le
    dsimp only [g]
    rw [norm_signedIntegrand hs0, affineTail]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (htail s hs) (centered_tilt_bounds hn hs0).1 (abs_nonneg _)
        (by positivity) |>.trans_eq (mul_one _)) (rayWeight_nonneg n hs0)
  have htotal := piecewise_upper_bound hg hp (affineTail_integrable hn) hp0 hloc htail'
  apply (div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) hmass.le).trans_lt
  exact (div_le_div_of_nonneg_right htotal hmass.le).trans_lt (by
    rw [add_div, hpInt]
    exact add_lt_add_of_le_of_lt le_rfl (covariance_tail_integral_bound hn))

/-- The successive-size bound (12) for the actual normalized near-ray mean.
The estimate holds throughout the interior parameter range. -/
theorem nearMean_step_lt_four_div {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d) :
    ‖nearMean d (n + 1) - nearMean d n‖ < 4 / (n : ℝ) := by
  have hn0 : 0 < n := by lia
  have h₀ := weighted_sub (nearAmplitude_weighted_integrable hd hD hn0)
    (weighted_const_integrable hn0 1)
  have h₁ := weighted_sub (nearAmplitude_weighted_integrable hd hD (Nat.succ_pos n))
    (weighted_const_integrable (Nat.succ_pos n) 1)
  have hbound := signed_integral_envelope hn (signed_integrable h₀ h₁)
    (A := (n : ℝ) / 2 + 11) (B := (n : ℝ) / 2 + 1) (C := 0)
    (by positivity) (by positivity) le_rfl
    (fun s hs => by simpa using nearAmplitude_sixth_error hd hD hS hL hs.1.le hs.2)
    (fun s hs => nearAmplitude_tail_error hd hD hS hL ((by norm_num : (0 : ℝ) ≤ 1 / 6).trans hs.le))
  rw [nearMean_step_signed hd hD hn0 1, norm_div, norm_neg, norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (mass_pos hn0) (tiltAverage_pos hn)), ← div_div]
  simp only [zero_mul, add_zero] at hbound
  exact ((div_lt_div_iff_of_pos_right (tiltAverage_pos hn)).mpr hbound).trans
    (broad_covariance_numeric hn)

private theorem conjugate_weighted_integrable {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    IntegrableOn (weighted n (nearConjugateRatio d)) (Ioi 0) := by
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  let K : ℝ≥0 := ⟨(n : ℝ) / 8, by positivity⟩
  have hLip : LipschitzOnWith K (nearConjugateRatio d) (Ioi 0) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    change dist (nearConjugateRatio d s) (nearConjugateRatio d t) ≤
      ((n : ℝ) / 8) * dist s t
    simpa only [dist_eq_norm, Real.norm_eq_abs] using
      nearConjugateRatio_lipschitz hd hD hS (mem_Ioi.mp hs).le (mem_Ioi.mp ht).le
  have hw : ContinuousOn (rayWeight n) (Ioi 0) := by
    unfold rayWeight
    exact Real.continuous_sqrt.continuousOn.div
      ((continuous_const.add continuous_id).pow _).continuousOn
      (fun s (hs : 0 < s) => by positivity)
  have hw' : ContinuousOn (fun s => (rayWeight n s : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn hw
  have hmeas : AEStronglyMeasurable (weighted n (nearConjugateRatio d))
      (volume.restrict (Ioi 0)) :=
    (hw'.mul hLip.continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hEnv := (affine_moment (n := n) (by linarith) 1 ((n : ℝ) / 8)).1
  apply hEnv.mono' hmeas
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
  have hs₀ : 0 ≤ s := (mem_Ioi.mp hs).le
  rw [weighted, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (rayWeight_nonneg n hs₀)]
  calc
    _ ≤ rayWeight n s * (1 + (n : ℝ) * s / 8) :=
      mul_le_mul_of_nonneg_left (nearConjugateRatio_norm_le hd hD hS hs₀) (rayWeight_nonneg n hs₀)
    _ = _ := by ring

private theorem signed_linear_moment {n : ℕ} (hn : 150 ≤ n) (s₀ : ℝ) :
    IntegrableOn (fun s => (s - s₀) * signedWeight n s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), (s - s₀) * signedWeight n s) =
        mass n * tiltAverage n * (moment n 1 - moment (n + 1) 1) := by
  have hraw (m : ℕ) (hm : 150 ≤ m) :
      IntegrableOn (fun s => (s - s₀) * rayWeight m s) (Ioi 0) ∧
        (∫ s in Ioi (0 : ℝ), (s - s₀) * rayWeight m s) = mass m * (moment m 1 - s₀) := by
    have hmR : (150 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : 0 < m := by lia
    have h0 : IntegrableOn (rayWeight m) (Ioi 0) := by
      simpa using integrableOn_moment (n := m) (j := 0) (by norm_num; linarith)
    have h1 : IntegrableOn (fun s => s * rayWeight m s) (Ioi 0) := by
      simpa using integrableOn_moment (n := m) (j := 1) (by norm_num; linarith)
    have heq (s : ℝ) : (s - s₀) * rayWeight m s = s * rayWeight m s - s₀ * rayWeight m s := by ring
    constructor
    · exact IntegrableOn.congr_fun (h1.sub (h0.const_mul s₀))
        (fun s _ => (heq s).symm) measurableSet_Ioi
    · have hraw1 : (∫ s in Ioi (0 : ℝ), s * rayWeight m s) = rawMoment m 1 := by
        simp only [rawMoment, pow_one]
      rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => heq s),
        integral_sub h1 (h0.const_mul s₀), integral_const_mul, hraw1, ← mass]
      unfold moment
      field_simp [(mass_pos hm0).ne']
  obtain ⟨h0, h0i⟩ := hraw n hn
  obtain ⟨h1, h1i⟩ := hraw (n + 1) (by lia)
  have heq (s : ℝ) : (s - s₀) * signedWeight n s =
      tiltAverage n * ((s - s₀) * rayWeight n s) - (s - s₀) * rayWeight (n + 1) s := by
    unfold signedWeight
    ring
  constructor
  · exact IntegrableOn.congr_fun ((h0.const_mul (tiltAverage n)).sub h1)
      (fun s _ => (heq s).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => heq s),
      integral_sub (h0.const_mul (tiltAverage n)) h1, integral_const_mul, h0i, h1i,
      mass_succ (by lia : 0 < n)]
    change tiltAverage n * (mass n * (moment n 1 - s₀)) -
      tiltAverage n * mass n * (moment (n + 1) 1 - s₀) = _
    ring

private theorem sign_center {n : ℕ} (hn : 150 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (s - ((tiltAverage n)⁻¹ - 1)) * signedWeight n s := by
  let η := tiltAverage n
  have hη : 0 < η := tiltAverage_pos hn
  have hbase : 0 < 1 + s := by positivity
  have heq : η - (1 + s)⁻¹ = η * (s - (η⁻¹ - 1)) / (1 + s) := by
    field_simp [hη.ne', hbase.ne']
    ring
  rw [signedWeight_eq, heq]
  have hform : (s - (η⁻¹ - 1)) * (η * (s - (η⁻¹ - 1)) / (1 + s) * rayWeight n s) =
      (s - (η⁻¹ - 1)) ^ 2 * (η / (1 + s) * rayWeight n s) := by ring
  rw [hform]
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (div_nonneg hη.le hbase.le) (rayWeight_nonneg n hs))

private theorem conjugate_signed_integral {d : ℝ} {n : ℕ} (hd : 0 < d) (hD : d < 1)
    (hn : 150 ≤ n) (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2))
    (hc : IntegrableOn (signedIntegrand n
      (fun s => nearConjugateRatio d s - nearConjugateRatio d ((tiltAverage n)⁻¹ - 1))) (Ioi 0)) :
    ‖∫ s in Ioi (0 : ℝ), signedIntegrand n
      (fun s => nearConjugateRatio d s - nearConjugateRatio d ((tiltAverage n)⁻¹ - 1)) s‖ /
      (mass n * tiltAverage n) ≤ 1 / (4 * (n : ℝ)) := by
  let s₀ := (tiltAverage n)⁻¹ - 1
  let f := fun s => signedIntegrand n (fun t => nearConjugateRatio d t - nearConjugateRatio d s₀) s
  have hs₀ : 0 ≤ s₀ := sub_nonneg.mpr
    ((one_le_inv₀ (tiltAverage_pos hn)).mpr (tiltAverage_le_one n))
  have hmass := mul_pos (mass_pos (by lia : 0 < n)) (tiltAverage_pos hn)
  obtain ⟨hlin, hlinInt⟩ := signed_linear_moment hn s₀
  have hle : ‖∫ s in Ioi (0 : ℝ), f s‖ ≤
      (n : ℝ) / 8 * (mass n * tiltAverage n * (moment n 1 - moment (n + 1) 1)) := by
    rw [← hlinInt, ← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply setIntegral_mono_on hc.norm (hlin.const_mul ((n : ℝ) / 8)) measurableSet_Ioi
    intro s hs
    have hs' : 0 ≤ s := (mem_Ioi.mp hs).le
    change ‖(signedWeight n s : ℂ) * (nearConjugateRatio d s - nearConjugateRatio d s₀)‖ ≤ _
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |signedWeight n s| * ((n : ℝ) / 8 * |s - s₀|) :=
        mul_le_mul_of_nonneg_left (nearConjugateRatio_lipschitz hd hD hS hs' hs₀) (abs_nonneg _)
      _ = (n : ℝ) / 8 * (|(s - s₀) * signedWeight n s|) := by rw [abs_mul]; ring
      _ = _ := by rw [abs_of_nonneg (sign_center hn hs')]
  apply (div_le_iff₀ hmass).mpr
  apply hle.trans
  rw [show (n : ℝ) / 8 * (mass n * tiltAverage n * (moment n 1 - moment (n + 1) 1)) =
    ((n : ℝ) / 8 * (moment n 1 - moment (n + 1) 1)) * (mass n * tiltAverage n) by ring]
  exact mul_le_mul_of_nonneg_right (conjugate_moment_gap_bound hn) hmass.le

private theorem nearConjugate_error_global {d s : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) (hL : 2 ≤ (n : ℝ) * d) (hs : 0 ≤ s) :
    ‖nearAmplitude d s - nearConjugateRatio d s‖ ≤
      (2 * (n : ℝ) + 1) * (1 + (n : ℝ) * s / 8) := by
  calc
    _ ≤ ‖nearAmplitude d s‖ + ‖nearConjugateRatio d s‖ := norm_sub_le _ _
    _ ≤ 2 * (n : ℝ) * (1 + (n : ℝ) * s / 8) + (1 + (n : ℝ) * s / 8) :=
      add_le_add (nearAmplitude_global hd hD hS hL hs) (nearConjugateRatio_norm_le hd hD hS hs)
    _ = _ := by ring

/-- The successive-size bound (11) for the actual normalized near-ray mean.
The condition 1 / 2 ≤ d covers the entire small-angle sector. -/
theorem nearMean_step_lt_one_div {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n) (hdHalf : 1 / 2 ≤ d)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    ‖nearMean d (n + 1) - nearMean d n‖ < 1 / (n : ℝ) := by
  let g := nearConjugateRatio d
  let s₀ := (tiltAverage n)⁻¹ - 1
  let f := fun s => nearAmplitude d s - g s
  let c := fun s => g s - g s₀
  have hn0 : 0 < n := by lia
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 2 ≤ (n : ℝ) * d :=
    (by norm_num : (2 : ℝ) ≤ 150 * (1 / 2)).trans
      (mul_le_mul hnR hdHalf (by norm_num) (by positivity))
  have hS' : 2 ≤ ((n + 1 : ℕ) : ℝ) * Real.sqrt (1 - d ^ 2) :=
    hS.trans (mul_le_mul_of_nonneg_right (by push_cast; linarith) (Real.sqrt_nonneg _))
  have hg0 := conjugate_weighted_integrable hd hD hn hS
  have hg1 := conjugate_weighted_integrable hd hD (by lia) hS'
  have hf : IntegrableOn (signedIntegrand n f) (Ioi 0) := signed_integrable
    (weighted_sub (nearAmplitude_weighted_integrable hd hD hn0) hg0)
    (weighted_sub (nearAmplitude_weighted_integrable hd hD (Nat.succ_pos n)) hg1)
  have hc : IntegrableOn (signedIntegrand n c) (Ioi 0) := signed_integrable
    (weighted_sub hg0 (weighted_const_integrable hn0 (g s₀)))
    (weighted_sub hg1 (weighted_const_integrable (Nat.succ_pos n) (g s₀)))
  have hF := signed_integral_envelope hn hf
    (A := 11) (B := 1 + 11 * (n : ℝ) / 8) (C := (n : ℝ) / 8)
    (by norm_num) (by positivity) (by positivity)
    (fun s hs => nearAmplitude_conjugate_error hd hD hdHalf hS hs.1.le hs.2)
    (fun s hs => nearConjugate_error_global hd hD hS hL
      ((by norm_num : (0 : ℝ) ≤ 1 / 6).trans hs.le))
  have hF' : ‖∫ s in Ioi (0 : ℝ), signedIntegrand n f s‖ / (mass n * tiltAverage n) <
      3 / (4 * (n : ℝ)) := by
    rw [← div_div]
    exact ((div_lt_div_iff_of_pos_right (tiltAverage_pos hn)).mpr hF).trans
      (small_covariance_numeric hn)
  have hC := conjugate_signed_integral hd hD hn hS hc
  have hmass := mul_pos (mass_pos hn0) (tiltAverage_pos hn)
  have heq (s : ℝ) : signedIntegrand n (fun t => nearAmplitude d t - g s₀) s =
      signedIntegrand n f s + signedIntegrand n c s := by
    simp only [signedIntegrand, f, c]
    ring
  rw [nearMean_step_signed hd hD hn0 (g s₀), norm_div, norm_neg,
    norm_real, Real.norm_eq_abs, abs_of_pos hmass,
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => heq s), integral_add hf hc]
  apply (div_le_div_of_nonneg_right (norm_add_le _ _) hmass.le).trans_lt
  rw [add_div]
  exact (add_lt_add_of_lt_of_le hF' hC).trans_le (by ring_nf; linarith)

/-- The cubic pointwise loss and affine tail give the integrated real-part margin. -/
private theorem nearConjugate_loss_integral_lt {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n) (hdHalf : 1 / 2 ≤ d)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    (∫ s in Ioi (0 : ℝ),
      ‖weighted n (fun t => nearAmplitude d t - nearConjugateRatio d t) s‖) /
        mass n < 3 / 20 := by
  let A : ℝ := 11
  let B : ℝ := 1 + 11 * (n : ℝ) / 8
  let C : ℝ := (n : ℝ) / 8
  let p (s : ℝ) := A * (s ^ (1 : ℕ) * rayWeight n s) +
    B * (s ^ (2 : ℕ) * rayWeight n s) + C * (s ^ (3 : ℕ) * rayWeight n s)
  let f := fun s => nearAmplitude d s - nearConjugateRatio d s
  let g := fun s => ‖weighted n f s‖
  have hn0 : 0 < n := by lia
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 2 ≤ (n : ℝ) * d :=
    (by norm_num : (2 : ℝ) ≤ 150 * (1 / 2)).trans
      (mul_le_mul hnR hdHalf (by norm_num) (by positivity))
  have hM := mass_pos hn0
  have hH : IntegrableOn (weighted n (nearAmplitude d)) (Ioi 0) :=
    nearAmplitude_weighted_integrable hd hD hn0
  have hc := conjugate_weighted_integrable hd hD hn hS
  have hf : IntegrableOn g (Ioi 0) := (weighted_sub hH hc).norm
  have h1 := (integrableOn_moment (n := n) (j := 1) (by norm_num; linarith)).const_mul A
  have h2 := (integrableOn_moment (n := n) (j := 2) (by norm_num; linarith)).const_mul B
  have h3 := (integrableOn_moment (n := n) (j := 3) (by norm_num; linarith)).const_mul C
  have h12 : IntegrableOn (fun s => A * (s ^ (1 : ℕ) * rayWeight n s) +
      B * (s ^ (2 : ℕ) * rayWeight n s)) (Ioi 0) := h1.add h2
  have hP : IntegrableOn p (Ioi 0) := h12.add h3
  have hPint : (∫ s in Ioi (0 : ℝ), p s) / mass n =
      A * moment n 1 + B * moment n 2 + C * moment n 3 := by
    change (∫ s in Ioi (0 : ℝ),
      (fun t => A * (t ^ (1 : ℕ) * rayWeight n t) + B * (t ^ (2 : ℕ) * rayWeight n t)) s +
      C * (s ^ (3 : ℕ) * rayWeight n s)) / mass n = _
    rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
      integral_const_mul, ← rawMoment, ← rawMoment, ← rawMoment]
    simp only [add_div, mul_div_assoc, moment]
  have hloc (s : ℝ) (hs : s ∈ Ioc 0 (1 / 6)) : g s ≤ p s := by
    simp only [g, weighted, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rayWeight_nonneg n hs.1.le)]
    calc
      _ ≤ rayWeight n s * (A * s + B * s ^ 2 + C * s ^ 3) :=
        mul_le_mul_of_nonneg_left
          (nearAmplitude_conjugate_error hd hD hdHalf hS hs.1.le hs.2) (rayWeight_nonneg n hs.1.le)
      _ = p s := by simp only [p, pow_one]; ring
  have htail (s : ℝ) (hs : s ∈ Ioi (1 / 6)) : g s ≤ affineTail n s := by
    have hs' : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 1 / 6).trans hs.le
    simp only [g, weighted, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (rayWeight_nonneg n hs')]
    exact (mul_le_mul_of_nonneg_left (nearConjugate_error_global hd hD hS hL hs')
      (rayWeight_nonneg n hs')).trans_eq (mul_comm _ _)
  have hgInt : (∫ s in Ioi (0 : ℝ), g s) / mass n < 3 / 20 := by
    have hcInt := piecewise_upper_bound hf hP (affineTail_integrable hn)
      (fun s hs => by
        have hw := rayWeight_nonneg n hs.le
        dsimp [p, A, B, C]
        positivity) hloc htail
    apply (div_le_div_of_nonneg_right hcInt hM.le).trans_lt
    rw [add_div, hPint]
    exact (add_lt_add_of_le_of_lt le_rfl (covariance_tail_integral_bound hn)).trans
      (small_real_part_numeric hn)
  exact hgInt

/-- The lower bound (10) on the actual near-ray mean in the small-angle sector. -/
theorem nearMean_re_gt_seventeen_twentieths {d : ℝ} {n : ℕ}
    (hd : 0 < d) (hD : d < 1) (hn : 150 ≤ n) (hdHalf : 1 / 2 ≤ d)
    (hS : 2 ≤ (n : ℝ) * Real.sqrt (1 - d ^ 2)) :
    17 / 20 < (nearMean d n).re := by
  let f := fun s => nearAmplitude d s - nearConjugateRatio d s
  let g := fun s => ‖weighted n f s‖
  have hn0 : 0 < n := by lia
  have hnR : (150 : ℝ) ≤ n := by exact_mod_cast hn
  have hM := mass_pos hn0
  have hH : IntegrableOn (weighted n (nearAmplitude d)) (Ioi 0) :=
    nearAmplitude_weighted_integrable hd hD hn0
  have hc := conjugate_weighted_integrable hd hD hn hS
  have hf : IntegrableOn g (Ioi 0) := (weighted_sub hH hc).norm
  have hgInt := nearConjugate_loss_integral_lt hd hD hn hdHalf hS
  have hr : IntegrableOn (fun s => (weighted n (nearAmplitude d) s).re) (Ioi 0) :=
    hH.re
  have hw : IntegrableOn (rayWeight n) (Ioi 0) := by
    simpa using integrableOn_moment (n := n) (j := 0) (by norm_num; linarith)
  have hloss : (∫ s in Ioi (0 : ℝ), rayWeight n s - (weighted n (nearAmplitude d) s).re) ≤
      ∫ s in Ioi (0 : ℝ), g s := by
    apply setIntegral_mono_on (hw.sub hr) hf measurableSet_Ioi
    intro s hs
    have hgs := nearConjugateRatio_one_le_re hd hD hs.le
    rw [Pi.sub_apply]
    simp only [g, weighted, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, norm_mul,
      norm_real, Real.norm_eq_abs, abs_of_nonneg (rayWeight_nonneg n hs.le)]
    rw [show rayWeight n s - rayWeight n s * (nearAmplitude d s).re =
      rayWeight n s * (1 - (nearAmplitude d s).re) by ring]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ (abs_re_le_norm (f s))) (rayWeight_nonneg n hs.le)
    apply le_trans ?_ (neg_le_abs ((f s).re))
    simp only [f, sub_re]
    linarith
  have hri : (∫ s in Ioi (0 : ℝ), (weighted n (nearAmplitude d) s).re) =
      (∫ s in Ioi (0 : ℝ), weighted n (nearAmplitude d) s).re := integral_re hH
  rw [integral_sub hw hr, hri, ← mass] at hloss
  have hnormalized := (div_le_div_of_nonneg_right hloss hM.le).trans_lt hgInt
  change 17 / 20 < ((∫ s in Ioi (0 : ℝ), weighted n (nearAmplitude d) s) / (mass n : ℂ)).re
  rw [div_ofReal_re]
  rw [sub_div, div_self hM.ne'] at hnormalized
  linarith only [hnormalized]

end RealRooted.CatalanWordPeaks.CutGeometry
