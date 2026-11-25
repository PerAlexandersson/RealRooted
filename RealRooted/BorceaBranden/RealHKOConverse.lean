module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.RealVectorSpace
public import RealRooted.BorceaBranden.MultivariateHKO
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

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
  let domain : Set (σ → ℂ) := Set.univ.pi fun _ => {u : ℂ | 0 < u.im}
  let ratioIm : (σ → ℂ) → ℝ := fun u =>
    ((MvPolynomial.eval u (complexifyMv F)) /
      (MvPolynomial.eval u (complexifyMv G))).im
  have hconnected : IsPreconnected domain :=
    isPreconnected_univ_pi fun _ => (convex_halfSpace_im_gt 0).isPreconnected
  have hGstable : MvRealStable G := hall.right.resolve_left hGzero
  have hcontinuous : ContinuousOn ratioIm domain :=
    Complex.continuous_im.comp_continuousOn
      ((MvPolynomial.continuous_eval _).continuousOn.div
        (MvPolynomial.continuous_eval _).continuousOn
        (fun u hu => hGstable u fun i => hu i (Set.mem_univ i)))
  have hsign := hconnected.sign_eq_of_continuousOn hcontinuous
    (fun u hu => complexifyMv_eval_ratio_im_ne_zero hall hGzero hindep
      (fun i => hu i (Set.mem_univ i)))
    (fun i _ => hz i) (fun i _ => hw i)
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, hsign]

/-- The converse orientation dichotomy in the multivariate
Hermite--Kakeya--Obreschkoff theorem: a real stable two-dimensional span has
one of the two proper-position orientations, with the zero pair separated.
This is Borcea--Brändén, arXiv:0809.0401, Theorem 1.9. -/
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

/-- The signed evaluation invariant of a real polynomial pair.  Its sign
records the proper-position orientation when every real linear combination
is stable or zero. -/
def mvPencilOrientationValue {σ : Type*} (z : σ → ℂ)
    (F G : MvPolynomial σ ℝ) : ℝ :=
  (MvPolynomial.eval z (complexifyMv F) *
    starRingEnd ℂ (MvPolynomial.eval z (complexifyMv G))).im

private theorem ratio_im_sign_eq_orientation_sign
    {a b : ℂ} (hb : b ≠ 0) :
    0 < (a / b).im ↔ 0 < (a * starRingEnd ℂ b).im := by
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  rw [← sub_div]
  rw [show a.re * -b.im + a.im * b.re = a.im * b.re - a.re * b.im by ring]
  exact div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hb)

/-- A positive orientation value selects the `G + iF` HKO orientation. -/
theorem AllComboMvRealStableOrZero.mvProperPosition_of_orientationValue_pos
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G)
    {z₀ : σ → ℂ} (hz₀ : ∀ i, 0 < (z₀ i).im)
    (hpos : 0 < mvPencilOrientationValue z₀ F G) :
    MvProperPosition G F := by
  have hGzero : G ≠ 0 := by
    intro hzero
    simp [mvPencilOrientationValue, hzero, complexifyMv] at hpos
  have hGstable : MvRealStable G := hall.right.resolve_left hGzero
  have hGz₀ := hGstable z₀ hz₀
  have hratioPos : 0 <
      (MvPolynomial.eval z₀ (complexifyMv F) /
        MvPolynomial.eval z₀ (complexifyMv G)).im :=
    (ratio_im_sign_eq_orientation_sign hGz₀).2 hpos
  have hindep : ∀ c : ℝ, F ≠ MvPolynomial.C c * G := by
    intro c heq
    subst F
    have hvalue :
        mvPencilOrientationValue z₀ (MvPolynomial.C c * G) G = 0 := by
      simp only [mvPencilOrientationValue, complexifyMv, map_mul,
        MvPolynomial.map_C, MvPolynomial.eval_C]
      change ((c : ℂ) * MvPolynomial.eval z₀ (complexifyMv G) *
        starRingEnd ℂ (MvPolynomial.eval z₀ (complexifyMv G))).im = 0
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.conj_re,
        Complex.conj_im]
      ring
    rw [hvalue] at hpos
    exact (lt_irrefl 0) hpos
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
  have hposz :=
    (ratio_im_has_constant_sign hall hGzero hindep hz₀ hz).1 hratioPos
  exact (not_lt_of_ge hposz.le) hnegz

/-- A negative orientation value selects the `F + iG` HKO orientation. -/
theorem AllComboMvRealStableOrZero.mvProperPosition_of_orientationValue_neg
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G)
    {z₀ : σ → ℂ} (hz₀ : ∀ i, 0 < (z₀ i).im)
    (hneg : mvPencilOrientationValue z₀ F G < 0) :
    MvProperPosition F G := by
  apply hall.comm.mvProperPosition_of_orientationValue_pos hz₀
  unfold mvPencilOrientationValue at hneg ⊢
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at hneg ⊢
  linarith

end RealRooted
