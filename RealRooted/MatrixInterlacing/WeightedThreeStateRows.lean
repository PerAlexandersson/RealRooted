module

public import RealRooted.MatrixInterlacing.WeightedThreeState
import RealRooted.PFPolynomial
import RealRooted.QuadraticInterlacingClosure

/-!
# Rows of the weighted three-state recurrence

This module completes the row consequences of the three-state construction from
issue #2088.  First, the middle coordinates of consecutive normalized states
interlace by Wagner's common-left cone.  We then rescale the parameters to give
the family with arbitrary positive geometric parameter `c`.

The matrix input is based on Brändén, *Unimodality, log-concavity,
real-rootedness and beyond*, Section 8, Theorem 8.5.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Consecutive middle coordinates of the normalized three-state recurrence
weakly interlace. -/
theorem weightedThreeState_P_interl_succ
    {b alpha d eta : ℝ} (hb : 0 ≤ b) (halpha : 0 ≤ alpha) (hd : 0 ≤ d)
    (heta : eta ≤ d) (hdb : d ≤ b) (halpha_b : alpha ≤ b) (n : ℕ) :
    Interl (weightedThreeState b alpha d eta n).P
      (weightedThreeState b alpha d eta (n + 1)).P := by
  have hstate :=
    weightedThreeState_interlacing hb halpha hd heta hdb halpha_b n
  have hPD : Interl (weightedThreeState b alpha d eta n).P
      (weightedThreeState b alpha d eta n).D := by
    have hpairs := hstate.interlacingSeq0
    rw [isInterlacingSeq0_iff_pairwise] at hpairs
    simpa [WeightedThreeState.toList] using
      List.Pairwise.rel_get_of_lt hpairs
        (a := ⟨1, by simp [WeightedThreeState.toList]⟩)
        (b := ⟨2, by simp [WeightedThreeState.toList]⟩) (by norm_num)
  have hP : HasNonnegCoeffs (weightedThreeState b alpha d eta n).P :=
    hstate.nonnegCoeffs _ (by simp [WeightedThreeState.toList])
  have hD : HasNonnegCoeffs (weightedThreeState b alpha d eta n).D :=
    hstate.nonnegCoeffs _ (by simp [WeightedThreeState.toList])
  have hPP : Interl (weightedThreeState b alpha d eta n).P
      (weightedThreeState b alpha d eta n).P :=
    Interl.refl fun hp0 =>
      hstate.splits (by simp [WeightedThreeState.toList]) hp0
  rw [show n + 1 = Nat.succ n by lia, weightedThreeState, weightedThreeStateStep]
  exact interl_add_right_of_common_left_of_nonneg hPP hPD hP hD

/-- The normalized middle coordinate has constant coefficient one. -/
theorem weightedThreeState_P_coeff_zero (b alpha d eta : ℝ) (n : ℕ) :
    (weightedThreeState b alpha d eta n).P.coeff 0 = 1 := by
  have hPD : (weightedThreeState b alpha d eta n).P.coeff 0 = 1 ∧
      (weightedThreeState b alpha d eta n).D.coeff 0 = 0 := by
    induction n with
    | zero => simp [weightedThreeState]
    | succ n ih =>
        simp only [weightedThreeState, weightedThreeStateStep]
        simp [ih.1, ih.2]
  exact hPD.1

/-- The weighted three-state matrix preserves all zero-aware nonnegative
interlacing triples exactly in the parameter region stated in issue #2088.
The criterion is Brändén's Theorem 8.5. -/
theorem weightedThreeStateMatrix_preserves_iff (b alpha d : ℝ) :
    PreservesInterlacingSeq0 3 (weightedThreeStateMatrix b alpha d) ↔
      0 ≤ b ∧ 0 ≤ alpha ∧ 0 ≤ d ∧ d ≤ b ∧ alpha ≤ b := by
  constructor
  · intro hpreserves
    have hnn := hpreserves.hasNonnegCoeffs
      (weightedThreeStateMatrix_rect b alpha d)
    have hb : 0 ≤ b := by
      have hCb : HasNonnegCoeffs (C b) := hnn [1, C b, C d]
        (by simp [weightedThreeStateMatrix]) (C b) (by simp)
      simpa using hCb 0
    have halpha : 0 ≤ alpha := by
      have hCalphaX : HasNonnegCoeffs (C alpha * X) := hnn [X, C alpha * X, 1]
        (by simp [weightedThreeStateMatrix]) (C alpha * X) (by simp)
      simpa using hCalphaX 1
    have hd : 0 ≤ d := by
      have hCd : HasNonnegCoeffs (C d) := hnn [1, C b, C d]
        (by simp [weightedThreeStateMatrix]) (C d) (by simp)
      simpa using hCd 0
    have hdb : d ≤ b := by
      have hcriterion := hpreserves.has2x2InterlacingProperty0
        (weightedThreeStateMatrix_rect b alpha d)
        (i₁ := ⟨0, by simp [weightedThreeStateMatrix]⟩)
        (i₂ := ⟨1, by simp [weightedThreeStateMatrix]⟩)
        (j₁ := ⟨1, by norm_num⟩) (j₂ := ⟨2, by norm_num⟩)
        (by norm_num) (by norm_num)
      have hinterl := hcriterion 1 1 (by norm_num) (by norm_num)
      simp only [weightedThreeStateMatrix, List.get_eq_getElem,
        List.getElem_cons_zero, List.getElem_cons_succ] at hinterl
      have hinterl' : Interl (C d * X + C (d + 1))
          (C b * X + C (b + 1)) := by
        convert hinterl using 1 <;> norm_num <;> ring
      by_cases hd0 : d = 0
      · simpa [hd0] using hb
      have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      have hleft0 : (C d * X + C (d + 1) : ℝ[X]) ≠ 0 := by
        intro hzero
        have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) hzero
        have : d = 0 := by simpa [Polynomial.coeff_one] using hcoeff
        exact hd0 this
      have hright0 : (C b * X + C (b + 1) : ℝ[X]) ≠ 0 := by
        intro hzero
        have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hzero
        simp at hcoeff
        nlinarith
      have hstrict : StrictInterl (C d * X + C (d + 1))
          (C b * X + C (b + 1)) := by
        exact hinterl'.toStrictInterl_of_ne hleft0 hright0
      have hbpos : 0 < b := by
        by_contra hbpos
        have hb0 : b = 0 := le_antisymm (le_of_not_gt hbpos) hb
        have hdegree := hstrict.natDegree_le
        rw [Polynomial.natDegree_linear hd0] at hdegree
        simp [hb0] at hdegree
      have hnormalized :=
        (hstrict.C_mul_left (inv_ne_zero hd0)).C_mul_right
          (inv_ne_zero hbpos.ne')
      have hnormalize_d : C d⁻¹ * (C d * X + C (d + 1)) =
          X + C ((d + 1) / d) := by
        rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul]
        field_simp
        simp only [C_1, one_mul]
      have hnormalize_b : C b⁻¹ * (C b * X + C (b + 1)) =
          X + C ((b + 1) / b) := by
        rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul]
        field_simp
        simp only [C_1, one_mul]
      have hlinear : StrictInterl (X + C ((d + 1) / d))
          (X + C ((b + 1) / b)) := by
        rwa [hnormalize_d, hnormalize_b] at hnormalized
      have hratio := StrictInterl.X_add_C_iff.mp hlinear
      rw [div_le_div_iff₀ hbpos hdpos] at hratio
      nlinarith
    have halpha_b : alpha ≤ b := by
      have hcriterion := hpreserves.has2x2InterlacingProperty0
        (weightedThreeStateMatrix_rect b alpha d)
        (i₁ := ⟨0, by simp [weightedThreeStateMatrix]⟩)
        (i₂ := ⟨2, by simp [weightedThreeStateMatrix]⟩)
        (j₁ := ⟨0, by norm_num⟩) (j₂ := ⟨1, by norm_num⟩)
        (by norm_num) (by norm_num)
      have hinterl := hcriterion 1 1 (by norm_num) (by norm_num)
      simp only [weightedThreeStateMatrix, List.get_eq_getElem,
        List.getElem_cons_zero, List.getElem_cons_succ] at hinterl
      have hinterl' : Interl (C (b + alpha) * X + C b)
          (C 2 * X + C 1) := by
        convert hinterl using 1
        · norm_num
          ring
        · rw [show (2 : ℝ) = 1 + 1 by norm_num, map_add, C_1]
          ring
      by_cases hslope0 : b + alpha = 0
      · nlinarith
      have hslope : 0 < b + alpha :=
        lt_of_le_of_ne (add_nonneg hb halpha) (Ne.symm hslope0)
      have hleft0 : (C (b + alpha) * X + C b : ℝ[X]) ≠ 0 := by
        intro hzero
        have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) hzero
        have : b + alpha = 0 := by
          simpa [Polynomial.coeff_one] using hcoeff
        exact hslope0 this
      have hright0 : (C 2 * X + C 1 : ℝ[X]) ≠ 0 := by
        intro hzero
        have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) hzero
        norm_num [Polynomial.coeff_one] at hcoeff
      have hstrict := hinterl'.toStrictInterl_of_ne hleft0 hright0
      have hnormalized :=
        (hstrict.C_mul_left (inv_ne_zero hslope0)).C_mul_right
          (by norm_num : (2 : ℝ)⁻¹ ≠ 0)
      have hnormalize_left : C (b + alpha)⁻¹ *
          (C (b + alpha) * X + C b) = X + C (b / (b + alpha)) := by
        rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul]
        field_simp
        simp only [C_1, one_mul]
      have hnormalize_right : C (2 : ℝ)⁻¹ * (C 2 * X + C 1) =
          X + C (1 / 2) := by
        rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul]
        norm_num
      have hlinear : StrictInterl (X + C (b / (b + alpha)))
          (X + C (1 / 2)) := by
        rwa [hnormalize_left, hnormalize_right] at hnormalized
      have hratio := StrictInterl.X_add_C_iff.mp hlinear
      have hmul : (1 / 2 : ℝ) * (b + alpha) ≤ b :=
        (le_div_iff₀ hslope).mp hratio
      nlinarith
    exact ⟨hb, halpha, hd, hdb, halpha_b⟩
  · rintro ⟨hb, halpha, hd, hdb, halpha_b⟩
    exact weightedThreeStateMatrix_preserves hb halpha hd hdb halpha_b

private lemma scaled_parameters_admissible
    {a b c eta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hbac : a * c / 2 ≤ b) (heta : eta ≤ min a (b / c)) :
    let A := a / c ^ 2
    let B := b / c ^ 3
    let E := eta / c ^ 2
    let d := min A B
    let alpha := A - d
    0 ≤ B ∧ 0 ≤ alpha ∧ 0 ≤ d ∧ E ≤ d ∧ d ≤ B ∧ alpha ≤ B := by
  dsimp only
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hc3 : 0 < c ^ 3 := pow_pos hc 3
  have hA : 0 ≤ a / c ^ 2 := div_nonneg ha hc2.le
  have hB : 0 ≤ b / c ^ 3 := div_nonneg hb hc3.le
  have hac : a * c ≤ 2 * b := by nlinarith [hbac]
  have hA_twoB : a / c ^ 2 ≤ 2 * (b / c ^ 3) := by
    calc
      a / c ^ 2 = (a * c) / c ^ 3 := by field_simp [hc.ne']
      _ ≤ (2 * b) / c ^ 3 := (div_le_div_iff_of_pos_right hc3).2 hac
      _ = 2 * (b / c ^ 3) := by ring
  have hE_A : eta / c ^ 2 ≤ a / c ^ 2 :=
    (div_le_div_iff_of_pos_right hc2).2 (heta.trans (min_le_left _ _))
  have hetaB : eta ≤ b / c := heta.trans (min_le_right _ _)
  have heta_mul : eta * c ≤ b := (le_div_iff₀ hc).mp hetaB
  have hE_B : eta / c ^ 2 ≤ b / c ^ 3 := by
    calc
      eta / c ^ 2 = (eta * c) / c ^ 3 := by field_simp [hc.ne']
      _ ≤ b / c ^ 3 := (div_le_div_iff_of_pos_right hc3).2 heta_mul
  refine ⟨hB, sub_nonneg.mpr (min_le_left _ _), le_min hA hB,
    le_min hE_A hE_B, min_le_right _ _, ?_⟩
  rcases le_total (a / c ^ 2) (b / c ^ 3) with hAB | hBA
  · simp [min_eq_left hAB, hB]
  · rw [min_eq_right hBA]
    linarith

/-- The row polynomial with geometric parameter `c`, obtained from the
normalized three-state recurrence by the substitution `w = c z`. -/
def weightedThreeStateRow (a b c eta : ℝ) (n : ℕ) : ℝ[X] :=
  let A := a / c ^ 2
  let B := b / c ^ 3
  let E := eta / c ^ 2
  let d := min A B
  C (c ^ n) * (weightedThreeState B (A - d) d E n).P

/-- Under the parameter inequalities from issue #2088, adjacent scaled rows
weakly interlace. -/
theorem weightedThreeStateRow_interl_succ
    {a b c eta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hbac : a * c / 2 ≤ b) (heta : eta ≤ min a (b / c)) (n : ℕ) :
    Interl (weightedThreeStateRow a b c eta n)
      (weightedThreeStateRow a b c eta (n + 1)) := by
  let A := a / c ^ 2
  let B := b / c ^ 3
  let E := eta / c ^ 2
  let d := min A B
  obtain ⟨hB, halpha, hd, hE, hdb, halpha_b⟩ :
      0 ≤ B ∧ 0 ≤ A - d ∧ 0 ≤ d ∧ E ≤ d ∧ d ≤ B ∧ A - d ≤ B := by
    simpa [A, B, E, d] using
      scaled_parameters_admissible ha hb hc hbac heta
  have hnormalized :=
    weightedThreeState_P_interl_succ hB halpha hd hE hdb halpha_b n
  have hscaled :=
    (hnormalized.C_mul_left_of_nonneg (pow_nonneg hc.le n)).C_mul_right_of_nonneg
      (pow_nonneg hc.le (n + 1))
  simpa [weightedThreeStateRow, A, B, E, d] using hscaled

/-- Every scaled row has nonnegative coefficients in the parameter region of
issue #2088. -/
theorem weightedThreeStateRow_hasNonnegCoeffs
    {a b c eta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hbac : a * c / 2 ≤ b) (heta : eta ≤ min a (b / c)) (n : ℕ) :
    HasNonnegCoeffs (weightedThreeStateRow a b c eta n) := by
  let A := a / c ^ 2
  let B := b / c ^ 3
  let E := eta / c ^ 2
  let d := min A B
  obtain ⟨hB, halpha, hd, hE, hdb, halpha_b⟩ :
      0 ≤ B ∧ 0 ≤ A - d ∧ 0 ≤ d ∧ E ≤ d ∧ d ≤ B ∧ A - d ≤ B := by
    simpa [A, B, E, d] using
      scaled_parameters_admissible ha hb hc hbac heta
  have hstate := weightedThreeState_interlacing hB halpha hd hE hdb halpha_b n
  have hP : HasNonnegCoeffs (weightedThreeState B (A - d) d E n).P :=
    hstate.nonnegCoeffs _ (by simp [WeightedThreeState.toList])
  simpa [weightedThreeStateRow, A, B, E, d] using
    hasNonnegCoeffs_C_mul (pow_nonneg hc.le n) hP

/-- The constant coefficient of the scaled row is `c ^ n`. -/
theorem weightedThreeStateRow_coeff_zero (a b c eta : ℝ) (n : ℕ) :
    (weightedThreeStateRow a b c eta n).coeff 0 = c ^ n := by
  rw [weightedThreeStateRow, coeff_C_mul, weightedThreeState_P_coeff_zero]
  ring

/-- Every scaled row is nonzero and real-rooted in the parameter region of
issue #2088. -/
theorem weightedThreeStateRow_isRealRooted
    {a b c eta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hbac : a * c / 2 ≤ b) (heta : eta ≤ min a (b / c)) (n : ℕ) :
    weightedThreeStateRow a b c eta n ≠ 0 ∧
      (weightedThreeStateRow a b c eta n).Splits := by
  let A := a / c ^ 2
  let B := b / c ^ 3
  let E := eta / c ^ 2
  let d := min A B
  obtain ⟨hB, halpha, hd, hE, hdb, halpha_b⟩ :
      0 ≤ B ∧ 0 ≤ A - d ∧ 0 ≤ d ∧ E ≤ d ∧ d ≤ B ∧ A - d ≤ B := by
    simpa [A, B, E, d] using
      scaled_parameters_admissible ha hb hc hbac heta
  have hstate := weightedThreeState_interlacing hB halpha hd hE hdb halpha_b n
  have hPsplits : (weightedThreeState B (A - d) d E n).P.Splits :=
    hstate.splits (by simp [WeightedThreeState.toList])
      (fun hP0 => by
        have hcoeff := weightedThreeState_P_coeff_zero B (A - d) d E n
        rw [hP0] at hcoeff
        norm_num at hcoeff)
  refine ⟨?_, ?_⟩
  · intro hzero
    have hcoeff := weightedThreeStateRow_coeff_zero a b c eta n
    rw [hzero] at hcoeff
    simp only [coeff_zero] at hcoeff
    exact (pow_ne_zero n hc.ne') hcoeff.symm
  · simpa [weightedThreeStateRow, A, B, E, d] using hPsplits.C_mul (c ^ n)

/-- All roots of every scaled row are strictly negative in the parameter
region of issue #2088. -/
theorem weightedThreeStateRow_roots_neg
    {a b c eta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hbac : a * c / 2 ≤ b) (heta : eta ≤ min a (b / c)) (n : ℕ) :
    ∀ r ∈ (weightedThreeStateRow a b c eta n).roots, r < 0 := by
  apply roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
  · exact weightedThreeStateRow_hasNonnegCoeffs ha hb hc hbac heta n
  · rw [weightedThreeStateRow_coeff_zero]
    exact pow_ne_zero n hc.ne'

/-- The first three scaled rows are `1`, `c`, and
`c ^ 2 + (a - eta) X`. -/
theorem weightedThreeStateRow_initial
    (a b c eta : ℝ) (hc : c ≠ 0) :
    weightedThreeStateRow a b c eta 0 = 1 ∧
      weightedThreeStateRow a b c eta 1 = C c ∧
      weightedThreeStateRow a b c eta 2 =
        C (c ^ 2) + C (a - eta) * X := by
  simp only [weightedThreeStateRow]
  have hinitial := weightedThreeState_P_initial
    (b / c ^ 3) (a / c ^ 2 - min (a / c ^ 2) (b / c ^ 3))
      (min (a / c ^ 2) (b / c ^ 3)) (eta / c ^ 2)
  rcases hinitial with ⟨hzero, hone, htwo⟩
  rw [hzero, hone, htwo]
  refine ⟨by simp, ?_, ?_⟩
  · simp
  · have hscalar : c ^ 2 *
        (a / c ^ 2 - min (a / c ^ 2) (b / c ^ 3) +
          min (a / c ^ 2) (b / c ^ 3) - eta / c ^ 2) = a - eta := by
      field_simp [hc]
      ring
    calc
      C (c ^ 2) *
          (1 + C (a / c ^ 2 - min (a / c ^ 2) (b / c ^ 3) +
            min (a / c ^ 2) (b / c ^ 3) - eta / c ^ 2) * X) =
        C (c ^ 2) + C (c ^ 2 *
          (a / c ^ 2 - min (a / c ^ 2) (b / c ^ 3) +
            min (a / c ^ 2) (b / c ^ 3) - eta / c ^ 2)) * X := by
            rw [C_mul]
            ring
      _ = C (c ^ 2) + C (a - eta) * X := by rw [hscalar]

end RealRooted
