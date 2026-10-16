module

public import RealRooted.BorceaBranden.RealFiniteSymbolSufficiency
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

open Set

noncomputable section

namespace RealRooted
namespace BorceaBranden

/-- The real-coefficient part of a shifted box. -/
def shiftedBoxRealPart {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    MvPolynomial.degreeOfLE σ ℝ κ :=
  ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
    (((MvPolynomial.boxChoose κ m.1 : ℂ) *
      ∏ i, W i ^ (κ i - m.1 i)).re) •
        MvPolynomial.basisDegreeOfLE κ m

/-- The imaginary-coefficient part of a shifted box. -/
def shiftedBoxImagPart {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    MvPolynomial.degreeOfLE σ ℝ κ :=
  ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
    (((MvPolynomial.boxChoose κ m.1 : ℂ) *
      ∏ i, W i ^ (κ i - m.1 i)).im) •
        MvPolynomial.basisDegreeOfLE κ m

/-- A shifted box is the complexification of its real part plus `i` times
the complexification of its imaginary part. -/
theorem complexify_shiftedBox_parts {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    complexifyDegreeBox κ (shiftedBoxRealPart κ W) +
        Complex.I • complexifyDegreeBox κ (shiftedBoxImagPart κ W) =
      shiftedBoxPolynomial κ W := by
  classical
  unfold shiftedBoxRealPart shiftedBoxImagPart shiftedBoxPolynomial
  rw [map_sum, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  have hsmul (r : ℝ) :
      complexifyDegreeBox κ
          (r • MvPolynomial.basisDegreeOfLE (R := ℝ) κ m) =
        (r : ℂ) • MvPolynomial.basisDegreeOfLE (R := ℂ) κ m := by
    rw [map_smul, complexifyDegreeBox_basis]
    rfl
  rw [hsmul, hsmul]
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul,
    MvPolynomial.coe_basisDegreeOfLE, MvPolynomial.smul_eq_C_mul]
  rw [← mul_assoc, ← map_mul, ← add_mul, ← map_add]
  congr 2
  exact Complex.ext (by simp) (by simp)

/-- Polynomial-valued form of `complexify_shiftedBox_parts`. -/
theorem complexifyMv_shiftedBox_parts {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    complexifyMv (shiftedBoxRealPart κ W).1 +
        MvPolynomial.C Complex.I *
          complexifyMv (shiftedBoxImagPart κ W).1 =
      (shiftedBoxPolynomial κ W).1 := by
  have hparts := congrArg Subtype.val (complexify_shiftedBox_parts κ W)
  simpa only [Submodule.coe_add, Submodule.coe_smul,
    coe_complexifyDegreeBox, MvPolynomial.smul_eq_C_mul] using hparts

/-- Conjugating every shift fixes the real part of a shifted box. -/
theorem shiftedBoxRealPart_conj {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    shiftedBoxRealPart κ (fun i => starRingEnd ℂ (W i)) =
      shiftedBoxRealPart κ W := by
  classical
  unfold shiftedBoxRealPart
  apply Finset.sum_congr rfl
  intro m _hm
  congr 1
  have hconj :
      (MvPolynomial.boxChoose κ m.1 : ℂ) *
          ∏ i, (starRingEnd ℂ (W i)) ^ (κ i - m.1 i) =
        starRingEnd ℂ
          ((MvPolynomial.boxChoose κ m.1 : ℂ) *
            ∏ i, W i ^ (κ i - m.1 i)) := by
    simp only [map_mul, map_prod, map_pow, map_natCast]
  rw [hconj, Complex.conj_re]

/-- Conjugating every shift negates the imaginary part of a shifted box. -/
theorem shiftedBoxImagPart_conj {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    shiftedBoxImagPart κ (fun i => starRingEnd ℂ (W i)) =
      -shiftedBoxImagPart κ W := by
  classical
  unfold shiftedBoxImagPart
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  have hconj :
      (MvPolynomial.boxChoose κ m.1 : ℂ) *
          ∏ i, (starRingEnd ℂ (W i)) ^ (κ i - m.1 i) =
        starRingEnd ℂ
          ((MvPolynomial.boxChoose κ m.1 : ℂ) *
            ∏ i, W i ^ (κ i - m.1 i)) := by
    simp only [map_mul, map_prod, map_pow, map_natCast]
  rw [hconj, Complex.conj_im]
  exact neg_smul _ _

/-- The real output part of a shifted-box fiber. -/
def shiftedBoxOutputReal {σ : Type*} [Fintype σ]
    (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (W : σ → ℂ) : MvPolynomial σ ℝ :=
  T (shiftedBoxRealPart κ W)

/-- The imaginary output part of a shifted-box fiber. -/
def shiftedBoxOutputImag {σ : Type*} [Fintype σ]
    (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (W : σ → ℂ) : MvPolynomial σ ℝ :=
  T (shiftedBoxImagPart κ W)

/-- The complexified operator sends a shifted box to the complex polynomial
formed from the two real output parts. -/
theorem complexificationDegreeBoxLinearMap_shiftedBox
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (W : σ → ℂ) :
    complexificationDegreeBoxLinearMap κ T (shiftedBoxPolynomial κ W) =
      complexifyMv (shiftedBoxOutputReal κ T W) +
        MvPolynomial.C Complex.I *
          complexifyMv (shiftedBoxOutputImag κ T W) := by
  rw [← complexify_shiftedBox_parts, map_add, map_smul,
    complexificationDegreeBoxLinearMap_complexify,
    complexificationDegreeBoxLinearMap_complexify]
  simp only [shiftedBoxOutputReal, shiftedBoxOutputImag,
    MvPolynomial.smul_eq_C_mul]

private theorem allCombo_of_stable_parts
    {σ : Type*} [Finite σ]
    {F G : MvPolynomial σ ℝ} {P : MvPolynomial σ ℂ}
    (hparts : complexifyMv F + MvPolynomial.C Complex.I * complexifyMv G = P)
    (hstable : MvUpperHalfPlaneStable P) :
    AllComboMvRealStableOrZero F G := by
  have hproper : MvProperPosition G F := by
    rw [MvProperPosition, hparts]
    exact hstable
  intro c d
  simpa only [add_comm] using hproper.allComboMvRealStableOrZero d c

/-- Applying a real stability preserver to the two parts of a shifted box
leaves every real output combination stable or zero. -/
theorem allCombo_shiftedBox_outputs_of_preserves
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : PreservesRealStabilityOnDegreeBox κ T)
    (W : σ → ℂ) (hW : ∀ i, 0 < (W i).im) :
    AllComboMvRealStableOrZero
      (shiftedBoxOutputReal κ T W) (shiftedBoxOutputImag κ T W) := by
  intro c d
  have hin := allCombo_of_stable_parts
    (complexifyMv_shiftedBox_parts κ W)
    (mvUpperHalfPlaneStable_shiftedBoxPolynomial κ W hW) c d
  let p : MvPolynomial.degreeOfLE σ ℝ κ :=
    c • shiftedBoxRealPart κ W + d • shiftedBoxImagPart κ W
  have hp : p.1 =
      MvPolynomial.C c * (shiftedBoxRealPart κ W).1 +
        MvPolynomial.C d * (shiftedBoxImagPart κ W).1 := by
    simp [p, MvPolynomial.smul_eq_C_mul]
  rw [← hp] at hin
  rcases hin with hzero | hstable
  · left
    have hpzero : p = 0 := Subtype.ext hzero
    have hout : c • T (shiftedBoxRealPart κ W) +
        d • T (shiftedBoxImagPart κ W) = 0 := by
      have hmap := congrArg T hpzero
      simpa [p, map_add, map_smul] using hmap
    simpa [shiftedBoxOutputReal, shiftedBoxOutputImag,
      MvPolynomial.smul_eq_C_mul] using hout
  · have hout := hT p hstable
    simpa [shiftedBoxOutputReal, shiftedBoxOutputImag, p, map_add,
      map_smul, MvPolynomial.smul_eq_C_mul] using hout

def upperBasePoint (σ : Type*) : σ → ℂ := fun _ => Complex.I

/-- The real orientation invariant of a shifted-symbol fiber, evaluated at
the all-`i` point in the output variables. -/
def shiftedBoxOrientationValue {σ : Type*} [Fintype σ]
    (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (W : σ → ℂ) : ℝ :=
  mvPencilOrientationValue (upperBasePoint σ)
    (shiftedBoxOutputReal κ T W) (shiftedBoxOutputImag κ T W)

private def evalComplexifyRealLinear {σ : Type*} (z : σ → ℂ) :
    MvPolynomial σ ℝ →ₗ[ℝ] ℂ where
  toFun p := MvPolynomial.eval z (complexifyMv p)
  map_add' p q := by simp [complexifyMv]
  map_smul' c p := by
    simp [complexifyMv, MvPolynomial.smul_eq_C_mul]

/-- The shifted-box orientation varies continuously along every affine path
of shifts.  This is the path-continuity input in the §4 homotopy argument. -/
theorem continuous_shiftedBoxOrientationValue_line
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (W V : σ → ℂ) :
    Continuous fun t : ℝ => shiftedBoxOrientationValue κ T
      (fun i => ((1 - t : ℝ) : ℂ) * W i + (t : ℂ) * V i) := by
  classical
  let e := (evalComplexifyRealLinear (upperBasePoint σ)).comp T
  change Continuous fun t : ℝ =>
    (e (shiftedBoxRealPart κ
      (fun i => ((1 - t : ℝ) : ℂ) * W i + (t : ℂ) * V i)) *
      starRingEnd ℂ
        (e (shiftedBoxImagPart κ
          (fun i => ((1 - t : ℝ) : ℂ) * W i + (t : ℂ) * V i)))).im
  unfold shiftedBoxRealPart shiftedBoxImagPart
  simp only [map_sum, map_smul]
  fun_prop

/-- Borcea--Brändén Proposition 4.1 / Corollary 1.10 in the form needed by
the homotopy: a zero orientation value in a stable real pencil gives a
nontrivial real linear relation between its two generators. -/
theorem exists_nontrivial_combo_eq_zero_of_orientationValue_eq_zero
    {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hall : AllComboMvRealStableOrZero F G)
    {z : σ → ℂ} (hz : ∀ i, 0 < (z i).im)
    (horient : mvPencilOrientationValue z F G = 0) :
    ∃ r s : ℝ, (r ≠ 0 ∨ s ≠ 0) ∧
      MvPolynomial.C r * F + MvPolynomial.C s * G = 0 := by
  by_cases hGzero : G = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, by simp [hGzero]⟩
  · have hGstable : MvRealStable G := hall.right.resolve_left hGzero
    let a := MvPolynomial.eval z (complexifyMv F)
    let b := MvPolynomial.eval z (complexifyMv G)
    have hb : b ≠ 0 := hGstable z hz
    have hnum : a.im * b.re - a.re * b.im = 0 := by
      have h' : a.re * -b.im + a.im * b.re = 0 := by
        simpa only [mvPencilOrientationValue, a, b, Complex.mul_im,
          Complex.conj_re, Complex.conj_im] using horient
      linarith
    have hratioIm : (a / b).im = 0 := by
      rw [Complex.div_im, ← sub_div, hnum, zero_div]
    let c : ℝ := (a / b).re
    have hratio : a / b = (c : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [c] using hratioIm
    have heval : a - (c : ℂ) * b = 0 := by
      apply (div_eq_iff hb).mp at hratio
      linear_combination hratio
    have hcombo := hall 1 (-c)
    have hpoly : MvPolynomial.C (1 : ℝ) * F + MvPolynomial.C (-c) * G =
        F + MvPolynomial.C (-c) * G := by simp
    rw [hpoly] at hcombo
    rcases hcombo with hzero | hstable
    · exact ⟨1, -c, Or.inl one_ne_zero, by simpa [hpoly] using hzero⟩
    · have hne := hstable z hz
      apply (hne ?_).elim
      simpa [a, b, complexifyMv, sub_eq_add_neg] using heval

/-- A nonzero complex multiple of a shifted box remains stable after adding a
sufficiently small positive real multiple of any complexified real input.
This is the robust perturbation estimate used in Borcea--Brändén §4. -/
theorem exists_pos_stable_smul_shiftedBox_add_complexify
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (W : σ → ℂ) (hW : ∀ i, 0 < (W i).im)
    (c : ℂ) (hc : c ≠ 0)
    (h : MvPolynomial.degreeOfLE σ ℝ κ) :
    ∃ ε : ℝ, 0 < ε ∧
      MvUpperHalfPlaneStable
        (c • shiftedBoxPolynomial κ W +
          (ε : ℂ) • complexifyDegreeBox κ h).1 := by
  obtain ⟨C, hC, hbound⟩ :=
    uniformlyDominatedByShiftedBox κ W hW (complexifyDegreeBox κ h)
  let ε : ℝ := ‖c‖ * (C + 1)⁻¹
  have hC1 : 0 < C + 1 := by linarith
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hε : 0 < ε := mul_pos hcnorm (inv_pos.mpr hC1)
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hS := mvUpperHalfPlaneStable_shiftedBoxPolynomial κ W hW z hz
  have hSnorm : 0 < ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ :=
    norm_pos_iff.mpr hS
  have hfrac : (C + 1)⁻¹ * C < 1 := by
    rw [inv_mul_eq_div]
    exact (div_lt_one hC1).mpr (by linarith)
  have hεC : ε * C < ‖c‖ := by
    calc
      ε * C = ‖c‖ * ((C + 1)⁻¹ * C) := by ring
      _ < ‖c‖ * 1 := mul_lt_mul_of_pos_left hfrac hcnorm
      _ = ‖c‖ := mul_one _
  have hεnorm : ‖(ε : ℂ)‖ = ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hsmall :
      ‖(ε : ℂ) *
          MvPolynomial.eval z (complexifyDegreeBox κ h).1‖ <
        ‖c * MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ := by
    rw [norm_mul, norm_mul, hεnorm]
    calc
      ε * ‖MvPolynomial.eval z (complexifyDegreeBox κ h).1‖ ≤
          ε * (C * ‖MvPolynomial.eval z
            (shiftedBoxPolynomial κ W).1‖) :=
        mul_le_mul_of_nonneg_left (hbound z hz) hε.le
      _ = (ε * C) *
          ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ := by ring
      _ < ‖c‖ *
          ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ :=
        mul_lt_mul_of_pos_right hεC hSnorm
  change MvPolynomial.eval z
      (c • (shiftedBoxPolynomial κ W).1 +
        (ε : ℂ) • (complexifyDegreeBox κ h).1) ≠ 0
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_C]
  intro hzero
  have heq : c * MvPolynomial.eval z (shiftedBoxPolynomial κ W).1 =
      -((ε : ℂ) * MvPolynomial.eval z (complexifyDegreeBox κ h).1) := by
    linear_combination hzero
  have hnormeq := congrArg norm heq
  rw [norm_neg] at hnormeq
  exact (ne_of_lt hsmall) hnormeq.symm

private theorem mvRealStableOrZero_of_nonzero_smul
    {σ : Type*} {ε : ℝ} (hε : ε ≠ 0) {P : MvPolynomial σ ℝ}
    (hP : MvRealStableOrZero (ε • P)) :
    MvRealStableOrZero P := by
  have hscaled := hP.C_mul ε⁻¹
  simpa only [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hε, map_one, one_mul] using hscaled

/-- If the shifted-symbol path reaches the phase-real intersection, the
robust perturbation argument forces every value of the operator to be real
stable or zero. -/
theorem forall_realStableOrZero_of_shiftedBoxOrientationValue_eq_zero
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : PreservesRealStabilityOnDegreeBox κ T)
    (W : σ → ℂ) (hW : ∀ i, 0 < (W i).im)
    (horient : shiftedBoxOrientationValue κ T W = 0) :
    ∀ h, MvRealStableOrZero (T h) := by
  let F := shiftedBoxRealPart κ W
  let G := shiftedBoxImagPart κ W
  let A := shiftedBoxOutputReal κ T W
  let B := shiftedBoxOutputImag κ T W
  have hall := allCombo_shiftedBox_outputs_of_preserves hT W hW
  have hz : ∀ i, 0 < (upperBasePoint σ i).im := by
    intro i
    simp [upperBasePoint]
  have horient' : mvPencilOrientationValue (upperBasePoint σ) A B = 0 := by
    exact horient
  obtain ⟨r, s, hrs, hrelation⟩ :=
    exists_nontrivial_combo_eq_zero_of_orientationValue_eq_zero
      hall hz horient'
  let K : MvPolynomial.degreeOfLE σ ℝ κ := r • F + s • G
  let L : MvPolynomial.degreeOfLE σ ℝ κ := r • G - s • F
  let c : ℂ := (r : ℂ) - Complex.I * (s : ℂ)
  have hc : c ≠ 0 := by
    intro hczero
    have hre : r = 0 := by
      have h := congrArg Complex.re hczero
      simpa only [c, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
        sub_zero, Complex.zero_re] using h
    have him : s = 0 := by
      have h := congrArg Complex.im hczero
      simpa only [c, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
        zero_add, zero_sub, Complex.zero_im, neg_eq_zero] using h
    rcases hrs with hr | hs
    · exact hr hre
    · exact hs him
  have hK : T K = 0 := by
    have hrelation' : r • A + s • B = 0 := by
      simpa only [MvPolynomial.smul_eq_C_mul] using hrelation
    simpa only [K, A, B, shiftedBoxOutputReal, shiftedBoxOutputImag,
      map_add, map_smul] using hrelation'
  intro h
  obtain ⟨ε, hε, hstable⟩ :=
    exists_pos_stable_smul_shiftedBox_add_complexify κ W hW c hc h
  let H : MvPolynomial.degreeOfLE σ ℝ κ := K + ε • h
  have hdecomp :
      (c • shiftedBoxPolynomial κ W +
          (ε : ℂ) • complexifyDegreeBox κ h).1 =
        complexifyMv H.1 + MvPolynomial.C Complex.I * complexifyMv L.1 := by
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      MvPolynomial.smul_eq_C_mul,
      ← complexifyMv_shiftedBox_parts κ W]
    simp only [H, K, L, F, G, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_smul, coe_complexifyDegreeBox, complexifyMv, map_add,
      map_sub, MvPolynomial.smul_eq_C_mul]
    simp only [map_mul, MvPolynomial.map_C]
    change MvPolynomial.C ((r : ℂ) - Complex.I * (s : ℂ)) *
          (MvPolynomial.map Complex.ofRealHom (shiftedBoxRealPart κ W).1 +
            MvPolynomial.C Complex.I *
              MvPolynomial.map Complex.ofRealHom (shiftedBoxImagPart κ W).1) +
        MvPolynomial.C (ε : ℂ) * MvPolynomial.map Complex.ofRealHom h.1 =
      (MvPolynomial.C (r : ℂ) *
          MvPolynomial.map Complex.ofRealHom (shiftedBoxRealPart κ W).1 +
        MvPolynomial.C (s : ℂ) *
          MvPolynomial.map Complex.ofRealHom (shiftedBoxImagPart κ W).1 +
        MvPolynomial.C (ε : ℂ) * MvPolynomial.map Complex.ofRealHom h.1) +
      MvPolynomial.C Complex.I *
        (MvPolynomial.C (r : ℂ) *
            MvPolynomial.map Complex.ofRealHom (shiftedBoxImagPart κ W).1 -
          MvPolynomial.C (s : ℂ) *
            MvPolynomial.map Complex.ofRealHom (shiftedBoxRealPart κ W).1)
    rw [map_sub, map_mul]
    ring_nf
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring
  have hproper : MvProperPosition L.1 H.1 := by
    rw [MvProperPosition, ← hdecomp]
    exact hstable
  have hH : MvRealStableOrZero H.1 :=
    hproper.allComboMvRealStableOrZero.right
  have hTH : MvRealStableOrZero (T H) := by
    rcases hH with hzero | hHstable
    · left
      have hHSubtype : H = 0 := Subtype.ext hzero
      rw [hHSubtype, map_zero]
    · exact hT H hHstable
  have hscaled : MvRealStableOrZero (ε • T h) := by
    have hTHvalue : T H = ε • T h := by
      simp only [H, map_add, map_smul, hK, zero_add]
    rwa [hTHvalue] at hTH
  exact mvRealStableOrZero_of_nonzero_smul hε.ne' hscaled

/-- On the preconnected open upper-half-plane shift set, a nowhere-zero
shifted-box orientation has constant sign.  The proof is the literal affine
path and intermediate-value argument omitted in Borcea--Brändén §4. -/
theorem shiftedBoxOrientationValue_pos_iff_of_ne_zero
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (hne : ∀ W, (∀ i, 0 < (W i).im) →
      shiftedBoxOrientationValue κ T W ≠ 0)
    {W V : σ → ℂ} (hW : ∀ i, 0 < (W i).im)
    (hV : ∀ i, 0 < (V i).im) :
    0 < shiftedBoxOrientationValue κ T W ↔
      0 < shiftedBoxOrientationValue κ T V := by
  let path : ℝ → σ → ℂ := fun t i =>
    ((1 - t : ℝ) : ℂ) * W i + (t : ℂ) * V i
  let orient : ℝ → ℝ := fun t => shiftedBoxOrientationValue κ T (path t)
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, 0 < (path t i).im := by
    intro t ht i
    rcases ht with ⟨ht0, ht1⟩
    simp only [path, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    have hleft : 0 ≤ (1 - t) * (W i).im :=
      mul_nonneg (sub_nonneg.mpr ht1) (hW i).le
    by_cases htzero : t = 0
    · simp [htzero, hW i]
    · have hright : 0 < t * (V i).im :=
        mul_pos (lt_of_le_of_ne ht0 (Ne.symm htzero)) (hV i)
      linarith
  have hcontinuous : ContinuousOn orient (Icc (0 : ℝ) 1) := by
    exact (continuous_shiftedBoxOrientationValue_line κ T W V).continuousOn
  have horientNe : ∀ t ∈ Icc (0 : ℝ) 1, orient t ≠ 0 := by
    intro t ht
    exact hne (path t) (hpath t ht)
  have hzero_of_neg_pos (h0 : orient 0 < 0) (h1 : 0 < orient 1) : False := by
    have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      hcontinuous (show 0 ∈ Icc (orient 0) (orient 1) from ⟨h0.le, h1.le⟩)
    obtain ⟨t, ht, htzero⟩ := himage
    exact horientNe t ht htzero
  have hzero_of_pos_neg (h0 : 0 < orient 0) (h1 : orient 1 < 0) : False := by
    have himage := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
      hcontinuous (show 0 ∈ Icc (orient 1) (orient 0) from ⟨h1.le, h0.le⟩)
    obtain ⟨t, ht, htzero⟩ := himage
    exact horientNe t ht htzero
  have hpath0 : path 0 = W := by funext i; simp [path]
  have hpath1 : path 1 = V := by funext i; simp [path]
  have horient0 : orient 0 = shiftedBoxOrientationValue κ T W := by
    simp [orient, hpath0]
  have horient1 : orient 1 = shiftedBoxOrientationValue κ T V := by
    simp [orient, hpath1]
  constructor
  · intro hpos
    rcases lt_or_gt_of_ne (hne V hV) with hneg | hposV
    · apply (hzero_of_pos_neg (by simpa [horient0] using hpos)
        (by simpa [horient1] using hneg)).elim
    · exact hposV
  · intro hpos
    rcases lt_or_gt_of_ne (hne W hW) with hneg | hposW
    · apply (hzero_of_neg_pos (by simpa [horient0] using hneg)
        (by simpa [horient1] using hpos)).elim
    · exact hposW

private theorem stable_shiftedBox_output_of_orientation_pos
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : PreservesRealStabilityOnDegreeBox κ T)
    (W : σ → ℂ) (hW : ∀ i, 0 < (W i).im)
    (hpos : 0 < shiftedBoxOrientationValue κ T W) :
    MvUpperHalfPlaneStable
      (complexificationDegreeBoxLinearMap κ T (shiftedBoxPolynomial κ W)) := by
  have hall := allCombo_shiftedBox_outputs_of_preserves hT W hW
  have hz : ∀ i, 0 < (upperBasePoint σ i).im := by
    intro i
    simp [upperBasePoint]
  have hproper := hall.mvProperPosition_of_orientationValue_pos hz hpos
  rw [complexificationDegreeBoxLinearMap_shiftedBox]
  exact hproper

private theorem stable_conj_shiftedBox_output_of_orientation_neg
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : PreservesRealStabilityOnDegreeBox κ T)
    (W : σ → ℂ) (hW : ∀ i, 0 < (W i).im)
    (hneg : shiftedBoxOrientationValue κ T W < 0) :
    MvUpperHalfPlaneStable
      (complexifyMv (shiftedBoxOutputReal κ T W) -
        MvPolynomial.C Complex.I *
          complexifyMv (shiftedBoxOutputImag κ T W)) := by
  have hall := allCombo_shiftedBox_outputs_of_preserves hT W hW
  have hz : ∀ i, 0 < (upperBasePoint σ i).im := by
    intro i
    simp [upperBasePoint]
  have hproper := hall.mvProperPosition_of_orientationValue_neg hz hneg
  have hscaled := hproper.C_mul (show -Complex.I ≠ 0 by simp)
  change MvUpperHalfPlaneStable
    (MvPolynomial.C (-Complex.I) *
      (complexifyMv (shiftedBoxOutputImag κ T W) +
        MvPolynomial.C Complex.I *
          complexifyMv (shiftedBoxOutputReal κ T W))) at hscaled
  convert hscaled using 1
  rw [map_neg, neg_mul, mul_add, ← mul_assoc, ← map_mul, Complex.I_mul_I,
    map_neg, map_one]
  ring

/-- Complexification commutes with simultaneous negation of the right block. -/
theorem complexifyMv_negRightVariablesHom
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℝ) :
    complexifyMv (MvPolynomial.negRightVariablesHom P) =
      MvPolynomial.negRightVariablesHom (complexifyMv P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [complexifyMv]
  | add P Q hP hQ =>
      unfold complexifyMv at hP hQ ⊢
      rw [map_add, map_add, map_add, hP, hQ]
      rw [map_add]
  | mul_X P i hP =>
      unfold complexifyMv at hP ⊢
      rw [map_mul, map_mul, map_mul, hP]
      cases i with
      | inl i => simp
      | inr i => simp

/-- The negative-right symbol of the complexification is the complexification
of the real negative-right symbol. -/
theorem algebraicSymbolNegRight_complexificationDegreeBoxLinearMap
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) :
    MvPolynomial.algebraicSymbolNegRight κ
        (complexificationDegreeBoxLinearMap κ T) =
      complexifyMv (MvPolynomial.algebraicSymbolNegRight κ T) := by
  rw [MvPolynomial.algebraicSymbolNegRight,
    algebraicSymbol_complexificationDegreeBoxLinearMap,
    MvPolynomial.algebraicSymbolNegRight,
    complexifyMv_negRightVariablesHom]

/-- Evaluating simultaneous right-block negation negates the right input. -/
theorem eval_negRightVariablesHom
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ)
    (z : τ → ℂ) (W : σ → ℂ) :
    MvPolynomial.eval (Sum.elim z W)
        (MvPolynomial.negRightVariablesHom P) =
      MvPolynomial.eval (Sum.elim z fun i => -W i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hP]
      cases i with
      | inl i => simp
      | inr i => simp

private theorem algebraicSymbol_realStable_of_orientation_pos
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : PreservesRealStabilityOnDegreeBox κ T)
    (hpos : ∀ W, (∀ i, 0 < (W i).im) →
      0 < shiftedBoxOrientationValue κ T W) :
    MvRealStable (MvPolynomial.algebraicSymbol κ T) := by
  change MvUpperHalfPlaneStable
    (complexifyMv (MvPolynomial.algebraicSymbol κ T))
  rw [← algebraicSymbol_complexificationDegreeBoxLinearMap]
  intro u hu
  let z : σ → ℂ := fun i => u (Sum.inl i)
  let W : σ → ℂ := fun i => u (Sum.inr i)
  have hz : ∀ i, 0 < (z i).im := fun i => hu (Sum.inl i)
  have hW : ∀ i, 0 < (W i).im := fun i => hu (Sum.inr i)
  have hfiber := stable_shiftedBox_output_of_orientation_pos
    hT W hW (hpos W hW)
  have heval := hfiber z hz
  rw [← eval_algebraicSymbol_eq_eval_shiftedBoxPolynomial] at heval
  have huEq : Sum.elim z W = u := by
    funext i
    cases i <;> rfl
  simpa only [huEq] using heval

private theorem algebraicSymbolNegRight_realStable_of_orientation_neg
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : PreservesRealStabilityOnDegreeBox κ T)
    (hneg : ∀ W, (∀ i, 0 < (W i).im) →
      shiftedBoxOrientationValue κ T W < 0) :
    MvRealStable (MvPolynomial.algebraicSymbolNegRight κ T) := by
  change MvUpperHalfPlaneStable
    (complexifyMv (MvPolynomial.algebraicSymbolNegRight κ T))
  rw [← algebraicSymbolNegRight_complexificationDegreeBoxLinearMap]
  intro u hu
  let z : σ → ℂ := fun i => u (Sum.inl i)
  let W : σ → ℂ := fun i => u (Sum.inr i)
  let U : σ → ℂ := fun i => -starRingEnd ℂ (W i)
  have hz : ∀ i, 0 < (z i).im := fun i => hu (Sum.inl i)
  have hW : ∀ i, 0 < (W i).im := fun i => hu (Sum.inr i)
  have hU : ∀ i, 0 < (U i).im := by
    intro i
    simp only [U, Complex.neg_im, Complex.conj_im, neg_neg]
    exact hW i
  have hconjU : (fun i => starRingEnd ℂ (U i)) = fun i => -W i := by
    funext i
    simp [U]
  have hreal : shiftedBoxRealPart κ (fun i => -W i) =
      shiftedBoxRealPart κ U := by
    rw [← hconjU, shiftedBoxRealPart_conj]
  have himag : shiftedBoxImagPart κ (fun i => -W i) =
      -shiftedBoxImagPart κ U := by
    rw [← hconjU, shiftedBoxImagPart_conj]
  have hfiber := stable_conj_shiftedBox_output_of_orientation_neg
    hT U hU (hneg U hU)
  have hfiberEq :
      complexificationDegreeBoxLinearMap κ T
          (shiftedBoxPolynomial κ fun i => -W i) =
        complexifyMv (shiftedBoxOutputReal κ T U) -
          MvPolynomial.C Complex.I *
            complexifyMv (shiftedBoxOutputImag κ T U) := by
    rw [complexificationDegreeBoxLinearMap_shiftedBox]
    simp only [shiftedBoxOutputReal, shiftedBoxOutputImag]
    rw [hreal, himag, map_neg]
    simp only [complexifyMv, map_neg, sub_eq_add_neg]
    ring
  rw [← hfiberEq] at hfiber
  have heval := hfiber z hz
  have huEq : Sum.elim z W = u := by
    funext i
    cases i <;> rfl
  rw [← huEq, MvPolynomial.algebraicSymbolNegRight,
    eval_negRightVariablesHom,
    eval_algebraicSymbol_eq_eval_shiftedBoxPolynomial]
  exact heval

/-- Borcea--Brändén, arXiv:0809.0401, §4: a real degree-box stability
preserver has stable-or-zero entire range, a real-stable algebraic symbol, or
a real-stable right-sign-reversed algebraic symbol. -/
theorem forall_realStableOrZero_or_symbol_or_negRight_of_preserves
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : PreservesRealStabilityOnDegreeBox κ T) :
    (∀ f, MvRealStableOrZero (T f)) ∨
      MvRealStable (MvPolynomial.algebraicSymbol κ T) ∨
      MvRealStable (MvPolynomial.algebraicSymbolNegRight κ T) := by
  by_cases hcross : ∃ W : σ → ℂ,
      (∀ i, 0 < (W i).im) ∧ shiftedBoxOrientationValue κ T W = 0
  · obtain ⟨W, hW, horient⟩ := hcross
    exact Or.inl
      (forall_realStableOrZero_of_shiftedBoxOrientationValue_eq_zero
        hT W hW horient)
  · have hne : ∀ W, (∀ i, 0 < (W i).im) →
        shiftedBoxOrientationValue κ T W ≠ 0 := by
      intro W hW horient
      exact hcross ⟨W, hW, horient⟩
    let W₀ : σ → ℂ := fun _ => Complex.I
    have hW₀ : ∀ i, 0 < (W₀ i).im := by
      intro i
      simp [W₀]
    rcases lt_or_gt_of_ne (hne W₀ hW₀) with hneg₀ | hpos₀
    · right
      right
      apply algebraicSymbolNegRight_realStable_of_orientation_neg hT
      intro W hW
      rcases lt_or_gt_of_ne (hne W hW) with hneg | hpos
      · exact hneg
      · have hposAtBase :=
          (shiftedBoxOrientationValue_pos_iff_of_ne_zero T hne hW₀ hW).2 hpos
        exact ((not_lt_of_ge hneg₀.le) hposAtBase).elim
    · right
      left
      apply algebraicSymbol_realStable_of_orientation_pos hT
      intro W hW
      exact (shiftedBoxOrientationValue_pos_iff_of_ne_zero T hne hW₀ hW).1 hpos₀

end BorceaBranden
end RealRooted
