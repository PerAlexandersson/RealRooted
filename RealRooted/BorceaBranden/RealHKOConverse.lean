import RealRooted.BorceaBranden.MultivariateHKO
import Mathlib.Topology.Order.IntermediateValue

open Set

noncomputable section

namespace RealRooted

private theorem complexifyMv_eval_ratio_im_ne_zero
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G)
    (hGzero : G ≠ 0)
    (hindep : ∀ c : ℝ, F ≠ MvPolynomial.C c * G)
    {z : σ → ℂ} (hz : ∀ i, 0 < (z i).im) :
    ((MvPolynomial.eval z (complexifyMv F)) /
      (MvPolynomial.eval z (complexifyMv G))).im ≠ 0 := by
  have hFzero : F ≠ 0 := by
    intro hzero
    exact hindep 0 (by simp [hzero])
  have hFstable : MvRealStable F := hall.left.resolve_left hFzero
  have hGstable : MvRealStable G := hall.right.resolve_left hGzero
  let a := MvPolynomial.eval z (complexifyMv F)
  let b := MvPolynomial.eval z (complexifyMv G)
  have hb : b ≠ 0 := hGstable z hz
  intro him
  let c : ℝ := (a / b).re
  have hratio : a / b = (c : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [c] using him
  have heval : a - (c : ℂ) * b = 0 := by
    apply (div_eq_iff hb).mp at hratio
    linear_combination hratio
  have hpoly : F + MvPolynomial.C (-c) * G ≠ 0 := by
    intro hzero
    apply hindep c
    have hneg : MvPolynomial.C (-c) * G = -(MvPolynomial.C c * G) := by
      simp
    rw [hneg] at hzero
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hzero)
  have hstable : MvRealStable (F + MvPolynomial.C (-c) * G) := by
    have hcombo := (hall 1 (-c)).resolve_left (by simpa using hpoly)
    simpa using hcombo
  have hne := hstable z hz
  apply hne
  simpa [sub_eq_add_neg, complexifyMv, a, b] using heval

private theorem ratio_im_has_constant_sign
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G)
    (hGzero : G ≠ 0)
    (hindep : ∀ c : ℝ, F ≠ MvPolynomial.C c * G)
    {z w : σ → ℂ} (hz : ∀ i, 0 < (z i).im)
    (hw : ∀ i, 0 < (w i).im) :
    0 < ((MvPolynomial.eval z (complexifyMv F)) /
        (MvPolynomial.eval z (complexifyMv G))).im ↔
      0 < ((MvPolynomial.eval w (complexifyMv F)) /
        (MvPolynomial.eval w (complexifyMv G))).im := by
  have hGstable : MvRealStable G := hall.right.resolve_left hGzero
  let path : ℝ → σ → ℂ := fun t i => ((1 - t : ℝ) : ℂ) * z i + (t : ℂ) * w i
  let ratioIm : ℝ → ℝ := fun t =>
    ((MvPolynomial.eval (path t) (complexifyMv F)) /
      (MvPolynomial.eval (path t) (complexifyMv G))).im
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, 0 < (path t i).im := by
    intro t ht i
    rcases ht with ⟨ht0, ht1⟩
    simp only [path, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    have hleft : 0 ≤ (1 - t) * (z i).im :=
      mul_nonneg (sub_nonneg.mpr ht1) (hz i).le
    by_cases htzero : t = 0
    · simp [htzero, hz i]
    · have hright : 0 < t * (w i).im :=
        mul_pos (lt_of_le_of_ne ht0 (Ne.symm htzero)) (hw i)
      linarith
  have hden : ∀ t ∈ Icc (0 : ℝ) 1,
      MvPolynomial.eval (path t) (complexifyMv G) ≠ 0 := by
    intro t ht
    exact hGstable (path t) (hpath t ht)
  have hcontinuous : ContinuousOn ratioIm (Icc (0 : ℝ) 1) := by
    have hpathContinuous : Continuous path := by fun_prop
    have hnumContinuous : Continuous fun t =>
        MvPolynomial.eval (path t) (complexifyMv F) :=
      (MvPolynomial.continuous_eval (complexifyMv F)).comp hpathContinuous
    have hdenContinuous : Continuous fun t =>
        MvPolynomial.eval (path t) (complexifyMv G) :=
      (MvPolynomial.continuous_eval (complexifyMv G)).comp hpathContinuous
    exact Complex.continuous_im.comp_continuousOn
      (hnumContinuous.continuousOn.div hdenContinuous.continuousOn hden)
  have hnonzero : ∀ t ∈ Icc (0 : ℝ) 1, ratioIm t ≠ 0 := by
    intro t ht
    exact complexifyMv_eval_ratio_im_ne_zero hall hGzero hindep (hpath t ht)
  have hzero_of_neg_pos (h0 : ratioIm 0 < 0) (h1 : 0 < ratioIm 1) : False := by
    have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcontinuous
      (show 0 ∈ Icc (ratioIm 0) (ratioIm 1) from ⟨h0.le, h1.le⟩)
    obtain ⟨t, ht, htzero⟩ := himage
    exact hnonzero t ht htzero
  have hzero_of_pos_neg (h0 : 0 < ratioIm 0) (h1 : ratioIm 1 < 0) : False := by
    have himage := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hcontinuous
      (show 0 ∈ Icc (ratioIm 1) (ratioIm 0) from ⟨h1.le, h0.le⟩)
    obtain ⟨t, ht, htzero⟩ := himage
    exact hnonzero t ht htzero
  have hpath0 : path 0 = z := by funext i; simp [path]
  have hpath1 : path 1 = w := by funext i; simp [path]
  have hratio0 : ratioIm 0 =
      ((MvPolynomial.eval z (complexifyMv F)) /
        (MvPolynomial.eval z (complexifyMv G))).im := by simp [ratioIm, hpath0]
  have hratio1 : ratioIm 1 =
      ((MvPolynomial.eval w (complexifyMv F)) /
        (MvPolynomial.eval w (complexifyMv G))).im := by simp [ratioIm, hpath1]
  constructor
  · intro hpos
    have hnz := complexifyMv_eval_ratio_im_ne_zero hall hGzero hindep hw
    rcases lt_or_gt_of_ne hnz with hneg | hposw
    · apply (hzero_of_pos_neg (by simpa [hratio0] using hpos)
        (by simpa [hratio1] using hneg)).elim
    · exact hposw
  · intro hpos
    have hnz := complexifyMv_eval_ratio_im_ne_zero hall hGzero hindep hz
    rcases lt_or_gt_of_ne hnz with hneg | hposz
    · apply (hzero_of_neg_pos (by simpa [hratio0] using hneg)
        (by simpa [hratio1] using hpos)).elim
    · exact hposz

/-- The converse orientation dichotomy in the multivariate
Hermite--Kakeya--Obreschkoff theorem: a real stable two-dimensional span has
one of the two proper-position orientations, with the zero pair separated. -/
theorem AllComboMvRealStableOrZero.eq_zero_or_properPosition
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G) :
    (F = 0 ∧ G = 0) ∨ MvProperPosition F G ∨ MvProperPosition G F := by
  by_cases hGzero : G = 0
  · by_cases hFzero : F = 0
    · exact Or.inl ⟨hFzero, hGzero⟩
    · right
      left
      have hFstable : MvRealStable F := hall.left.resolve_left hFzero
      intro z hz
      simpa [hGzero, complexifyMv] using
        (mul_ne_zero (show Complex.I ≠ 0 by simp) (hFstable z hz))
  · have hGstable : MvRealStable G := hall.right.resolve_left hGzero
    by_cases hdep : ∃ c : ℝ, F = MvPolynomial.C c * G
    · obtain ⟨c, rfl⟩ := hdep
      right
      left
      intro z hz
      have hGz := hGstable z hz
      have hscalar : 1 + Complex.I * Complex.ofReal c ≠ 0 := by
        intro hzero
        have hre := congrArg Complex.re hzero
        simp at hre
      simp only [complexifyMv, map_mul, MvPolynomial.map_C,
        MvPolynomial.eval_add, MvPolynomial.eval_C]
      have hc : Complex.ofRealHom c = Complex.ofReal c := rfl
      rw [hc]
      rw [show MvPolynomial.eval z (MvPolynomial.map Complex.ofRealHom G) +
          Complex.I *
            (Complex.ofReal c *
              MvPolynomial.eval z (MvPolynomial.map Complex.ofRealHom G)) =
          (1 + Complex.I * Complex.ofReal c) *
            MvPolynomial.eval z (MvPolynomial.map Complex.ofRealHom G) by ring]
      exact mul_ne_zero hscalar hGz
    · let z₀ : σ → ℂ := fun _ => Complex.I
      have hz₀ : ∀ i, 0 < (z₀ i).im := by simp [z₀]
      have hsign := complexifyMv_eval_ratio_im_ne_zero hall hGzero
        (fun c hc => hdep ⟨c, hc⟩) hz₀
      rcases lt_or_gt_of_ne hsign with hneg | hpos
      · right
        left
        intro z hz hzero
        have hGz := hGstable z hz
        have hratio :
            MvPolynomial.eval z (complexifyMv F) /
                MvPolynomial.eval z (complexifyMv G) = Complex.I := by
          apply (div_eq_iff hGz).2
          simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
            MvPolynomial.eval_C] at hzero
          have hIF : Complex.I * MvPolynomial.eval z (complexifyMv F) =
              -MvPolynomial.eval z (complexifyMv G) := by
            linear_combination hzero
          calc
            MvPolynomial.eval z (complexifyMv F) =
                (-Complex.I) *
                  (Complex.I * MvPolynomial.eval z (complexifyMv F)) := by
              rw [← mul_assoc]
              simp [Complex.I_mul_I]
            _ = (-Complex.I) * (-MvPolynomial.eval z (complexifyMv G)) := by
              rw [hIF]
            _ = Complex.I * MvPolynomial.eval z (complexifyMv G) := by ring
        have hposz : 0 <
            (MvPolynomial.eval z (complexifyMv F) /
              MvPolynomial.eval z (complexifyMv G)).im := by
          rw [hratio]
          simp
        have hbasepos :=
          (ratio_im_has_constant_sign hall hGzero
            (fun c hc => hdep ⟨c, hc⟩) hz₀ hz).2 hposz
        exact (not_lt_of_ge hneg.le) hbasepos
      · right
        right
        intro z hz hzero
        have hratio :
            MvPolynomial.eval z (complexifyMv F) /
                MvPolynomial.eval z (complexifyMv G) = -Complex.I := by
          apply (div_eq_iff (hGstable z hz)).2
          simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
            MvPolynomial.eval_C] at hzero
          linear_combination hzero
        have hnegz :
            (MvPolynomial.eval z (complexifyMv F) /
              MvPolynomial.eval z (complexifyMv G)).im < 0 := by
          rw [hratio]
          simp
        have hbasepos :=
          (ratio_im_has_constant_sign hall hGzero
            (fun c hc => hdep ⟨c, hc⟩) hz₀ hz).1 hpos
        exact (not_lt_of_ge hbasepos.le) hnegz

end RealRooted
