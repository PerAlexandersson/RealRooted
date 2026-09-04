import RealRooted.Bezoutian.WronskianConverse

/-!
# Low-degree Bezoutian characterization

Degree-zero, linear, and quadratic positive-definiteness equivalences and the
final all-degree strict Bezoutian characterization.
-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

lemma StrictPrecSameDegree.of_bezoutMatrix_posDef_three_le
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 3) (hq_deg : q.natDegree = n + 3)
    (h : (bezoutMatrix (n + 3) q p).PosDef) :
    StrictPrecSameDegree p q :=
  let ⟨hp_s, hq_s⟩ := bezoutMatrix.splits_of_posDef hp_pos hq_pos hp_deg hq_deg h
  StrictPrecSameDegree.of_splits_and_posDef hp_pos hq_pos hp_deg hq_deg hp_s hq_s h

lemma _root_.Matrix.PosDef.det_pos_fin_two_entries {a b c : ℝ}
    (h : (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    0 < a * c - b * b := by
  have hdiag : 0 < (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := h.diag_pos
  have : 0 < a := by simpa using hdiag
  have hx : ![-b, a] ≠ (0 : Fin 2 → ℝ) := fun hzero => by simp_all
  have hquad := h.dotProduct_mulVec_pos hx
  norm_num [dotProduct, Matrix.mulVec] at hquad
  nlinarith

lemma bezoutMatrix.det_pos_of_quadratic_posDef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    0 < ((a + c) * (b * d) - (b + d) * (a * c)) * (b + d - (a + c)) -
    (b * d - a * c) * (b * d - a * c) := by
  rw [bezoutMatrix.quadratic_eq_fin_two] at h
  exact h.det_pos_fin_two_entries

lemma bezoutMatrix.det_factor_pos_of_quadratic_posDef {a b c d : ℝ}
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    0 < (a - b) * (a - d) * (b - c) * (c - d) := by
  have hdet := bezoutMatrix.det_pos_of_quadratic_posDef h
  grind

/-- For ordered quadratic factors, positive semidefiniteness of the Bezoutian
extracts the expected interleaving inequalities on the constants. -/
lemma bezoutMatrix.const_interleaves_of_quadratic_posSemidef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosSemidef) :
    a ≤ b ∧ b ≤ c ∧ c ≤ d := by
  have h_sum := bezoutMatrix.sum_le_of_quadratic_posSemidef h
  have h_det := bezoutMatrix.det_factor_nonneg_of_quadratic_posSemidef h
  have hab : a ≤ b := by
    by_contra hnot
    have hba : b < a := not_le.mp hnot
    have hcd : c < d := by linarith
    have had : a < d := lt_of_le_of_lt hac hcd
    have hbc : b < c := lt_of_lt_of_le hba hac
    have h₁ : (a - b) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hba) (sub_neg.mpr had)
    have h₂ : 0 < (b - c) * (c - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hbc) (sub_neg.mpr hcd)
    nlinarith
  have hbc : b ≤ c := by
    by_contra hnot
    have hcb : c < b := not_le.mp hnot
    have hab' : a < b := lt_of_le_of_lt hac hcb
    have hcd : c < d := lt_of_lt_of_le hcb hbd
    have had : a < d := lt_of_le_of_lt hac hcd
    have h₁ : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h₂ : (b - c) * (c - d) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hcb) (sub_neg.mpr hcd)
    nlinarith
  have hcd : c ≤ d := by
    by_contra hnot
    have hdc : d < c := not_le.mp hnot
    have hab' : a < b := by linarith
    have had : a < d := lt_of_lt_of_le hab' hbd
    have hbc' : b < c := lt_of_le_of_lt hbd hdc
    have h₁ : 0 < (a - b) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hab') (sub_neg.mpr had)
    have h₂ : (b - c) * (c - d) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hbc') (sub_pos.mpr hdc)
    nlinarith
  simp_all

/-- Ordered constants give the positive-semidefinite quadratic Bezoutian. -/
lemma bezoutMatrix.const_strictInterleaves_of_quadratic_posDef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    a < b ∧ b < c ∧ c < d := by
  rcases bezoutMatrix.const_interleaves_of_quadratic_posSemidef hac hbd h.posSemidef with
    ⟨hab_le, hbc_le, hcd_le⟩
  have h_det := bezoutMatrix.det_factor_pos_of_quadratic_posDef h
  have hab_ne : a ≠ b := by
    rintro rfl
    simp_all
  have hbc_ne : b ≠ c := by
    rintro rfl
    simp_all
  have hcd_ne : c ≠ d := by
    rintro rfl
    simp_all
  grind

lemma bezoutMatrix.quadratic_posDef_two_of_const_strictInterleaves {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef := by
  rw [bezoutMatrix.quadratic_eq_fin_two]
  refine Matrix.posDef_fin_two_of_entries ?_ ?_
  · have hAeq : (a + c) * (b * d) - (b + d) * (a * c) =
        (b - a) * c ^ 2 + (d - c) * (b ^ 2 + (b - a) * (c - b)) := by ring
    rw [hAeq]
    have hba : 0 < b - a := sub_pos.mpr hab
    have hcb : 0 < c - b := sub_pos.mpr hbc
    have hdc : 0 < d - c := sub_pos.mpr hcd
    by_cases hc0 : c = 0
    · have hb0 : b ≠ 0 := by linarith
      have hb_pos : 0 < b ^ 2 + (b - a) * (c - b) :=
        add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hb0)
          (mul_nonneg hba.le hcb.le)
      nlinarith
    · have hleft : 0 < (b - a) * c ^ 2 :=
        mul_pos hba (sq_pos_of_ne_zero hc0)
      have h_nonneg : 0 ≤ (d - c) * (b ^ 2 + (b - a) * (c - b)) :=
        mul_nonneg hdc.le (add_nonneg (sq_nonneg b) (mul_nonneg hba.le hcb.le))
      nlinarith
  · have hdet_eq :
        ((a + c) * (b * d) - (b + d) * (a * c)) * (b + d - (a + c)) -
          (b * d - a * c) * (b * d - a * c) =
        (b - a) * (c - b) * (d - c) * (d - a) := by ring
    rw [hdet_eq]
    have : 0 < d - a := by linarith
    simp_all

lemma StrictPrecSameDegree.quadratic_of_const_strictInterleaves {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c)) := by
  refine ⟨isRealRooted_mul (Polynomial.isRealRooted_X_add_C b).1
            (Polynomial.isRealRooted_X_add_C b).2
            (Polynomial.isRealRooted_X_add_C d).1
            (Polynomial.isRealRooted_X_add_C d).2,
          isRealRooted_mul (Polynomial.isRealRooted_X_add_C a).1
            (Polynomial.isRealRooted_X_add_C a).2
            (Polynomial.isRealRooted_X_add_C c).1
            (Polynomial.isRealRooted_X_add_C c).2,
          by rw [natDegree_mul (Polynomial.isRealRooted_X_add_C b).1
                   (Polynomial.isRealRooted_X_add_C d).1,
                 natDegree_mul (Polynomial.isRealRooted_X_add_C a).1
                   (Polynomial.isRealRooted_X_add_C c).1]; simp,
          ?_⟩
  rw [Polynomial.roots_sort_mul_X_add_C_X_add_C (by linarith : b ≤ d),
    Polynomial.roots_sort_mul_X_add_C_X_add_C (by linarith : a ≤ c)]
  simp [*]

lemma StrictPrecSameDegree.quadratic_iff_const_strictInterleaves {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d) :
    StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c)) ↔
      a < b ∧ b < c ∧ c < d := by
  constructor
  · rintro ⟨_, _, _, halt⟩
    rw [Polynomial.roots_sort_mul_X_add_C_X_add_C hbd,
      Polynomial.roots_sort_mul_X_add_C_X_add_C hac] at halt
    simp_all
  · exact fun ⟨hab, hbc, hcd⟩ ↦
      StrictPrecSameDegree.quadratic_of_const_strictInterleaves hab hbc hcd

lemma StrictPrecSameDegree.of_bezoutMatrix_quadratic_posDef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef) :
    StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c)) :=
  let ⟨hab, hbc, hcd⟩ := bezoutMatrix.const_strictInterleaves_of_quadratic_posDef hac hbd h
  StrictPrecSameDegree.quadratic_of_const_strictInterleaves hab hbc hcd

lemma StrictPrecSameDegree.bezoutMatrix_quadratic_posDef {a b c d : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d)
    (h : StrictPrecSameDegree ((X + C b) * (X + C d)) ((X + C a) * (X + C c))) :
    (bezoutMatrix 2 ((X + C a) * (X + C c))
    ((X + C b) * (X + C d))).PosDef :=
  let ⟨hab, hbc, hcd⟩ :=
    (StrictPrecSameDegree.quadratic_iff_const_strictInterleaves hac hbd).mp h
  bezoutMatrix.quadratic_posDef_two_of_const_strictInterleaves hab hbc hcd

lemma StrictPrecSameDegree.bezoutMatrix_posDef_quadratic
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
    (hprec : StrictPrecSameDegree p q) :
    (bezoutMatrix 2 q p).PosDef := by
  obtain ⟨hp_ne, hp_splits⟩ := hprec.1
  obtain ⟨hq_ne, hq_splits⟩ := hprec.2.1
  obtain ⟨b, d, hbd, hp_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hp_splits hp_deg
  obtain ⟨a, c, hac, hq_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hq_splits hq_deg
  let mp : ℝ[X] := (X + C b) * (X + C d)
  let mq : ℝ[X] := (X + C a) * (X + C c)
  let u : ℝ := q.leadingCoeff
  let v : ℝ := p.leadingCoeff
  have hu : 0 < u := hq_pos
  have hv : 0 < v := hp_pos
  have hq_eq' : q = C u * mq := hq_eq
  have hp_eq' : p = C v * mp := hp_eq
  have hprec_monic : StrictPrecSameDegree mp mq :=
    (StrictPrecSameDegree.C_mul_C_mul_iff hv.ne' hu.ne').mp (by grind)
  have hmonic : (bezoutMatrix 2 mq mp).PosDef :=
    StrictPrecSameDegree.bezoutMatrix_quadratic_posDef hac hbd hprec_monic
  have hscaled : (bezoutMatrix 2 (C u * mq) (C v * mp)).PosDef :=
    (bezoutMatrix.C_mul_C_mul_posDef_iff (n := 2) (u := u) (v := v) hu hv).mpr hmonic
  grind

lemma StrictPrecSameDegree.of_bezoutMatrix_posDef_of_isRealRooted_quadratic
    {p q : ℝ[X]}
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
    (h : (bezoutMatrix 2 q p).PosDef) :
    StrictPrecSameDegree p q := by
  obtain ⟨b, d, hbd, hp_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hp_splits hp_deg
  obtain ⟨a, c, hac, hq_eq⟩ :=
    Polynomial.exists_sorted_linear_factors_of_isRealRooted_natDegree_two hq_splits hq_deg
  let mp : ℝ[X] := (X + C b) * (X + C d)
  let mq : ℝ[X] := (X + C a) * (X + C c)
  let u : ℝ := q.leadingCoeff
  let v : ℝ := p.leadingCoeff
  have hu : 0 < u := hq_pos
  have hv : 0 < v := hp_pos
  have hq_eq' : q = C u * mq := hq_eq
  have hp_eq' : p = C v * mp := hp_eq
  have hscaled : (bezoutMatrix 2 (C u * mq) (C v * mp)).PosDef := hp_eq' ▸ hq_eq' ▸ h
  have hmonic : (bezoutMatrix 2 mq mp).PosDef :=
    (bezoutMatrix.C_mul_C_mul_posDef_iff (n := 2) (u := u) (v := v) hu hv).mp hscaled
  have hprec_monic : StrictPrecSameDegree mp mq :=
    StrictPrecSameDegree.of_bezoutMatrix_quadratic_posDef hac hbd hmonic
  have hprec_scaled : StrictPrecSameDegree (C v * mp) (C u * mq) :=
    hprec_monic.C_mul_C_mul (ne_of_gt hv) (ne_of_gt hu)
  grind

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_of_isRealRooted_quadratic
    {p q : ℝ[X]}
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 2 q p).PosDef := by
  constructor
  · exact StrictPrecSameDegree.bezoutMatrix_posDef_quadratic
      hp_pos hq_pos hp_deg hq_deg
  · exact StrictPrecSameDegree.of_bezoutMatrix_posDef_of_isRealRooted_quadratic
      hp_splits hq_splits hp_pos hq_pos hp_deg hq_deg

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_zero
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 0) (hq_deg : q.natDegree = 0) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 0 q p).PosDef := by
  obtain ⟨hp_ne, hp_splits⟩ :=
    isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hp_pos.ne') hp_deg
  obtain ⟨hq_ne, hq_splits⟩ :=
    isRealRooted_of_deg_zero (leadingCoeff_ne_zero.mp hq_pos.ne') hq_deg
  constructor
  · intro hprec
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (bezoutMatrix.isHermitian _ _ _) ?_
    intro x hx
    exact False.elim (hx (funext fun i ↦ i.elim0))
  · intro _
    refine ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, hp_deg.trans hq_deg.symm, ?_⟩
    have hp_roots : p.roots.sort (· ≤ ·) = [] := by
      simp [Multiset.card_eq_zero.mp (hp_splits.natDegree_eq_card_roots.symm ▸ hp_deg)]
    have hq_roots : q.roots.sort (· ≤ ·) = [] := by
      simp [Multiset.card_eq_zero.mp (hq_splits.natDegree_eq_card_roots.symm ▸ hq_deg)]
    simp_all

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_one
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 1) (hq_deg : q.natDegree = 1) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 1 q p).PosDef := by
  rcases Polynomial.exists_pos_scalar_mul_X_add_C_of_natDegree_one hp_pos hp_deg with
    ⟨u, a, hu, hp_eq⟩
  rcases Polynomial.exists_pos_scalar_mul_X_add_C_of_natDegree_one hq_pos hq_deg with
    ⟨v, b, hv, hq_eq⟩
  rw [hp_eq, hq_eq]
  calc
    StrictPrecSameDegree (C u * (X + C a)) (C v * (X + C b))
        ↔ StrictPrecSameDegree (X + C a) (X + C b) :=
      StrictPrecSameDegree.C_mul_C_mul_iff (ne_of_gt hu) (ne_of_gt hv)
    _ ↔ (bezoutMatrix 1 (X + C b) (X + C a)).PosDef :=
      StrictPrecSameDegree.X_add_C_bezoutMatrix_posDef_iff_one (a := b) (b := a)
    _ ↔ (bezoutMatrix 1 (C v * (X + C b)) (C u * (X + C a))).PosDef :=
      (bezoutMatrix.C_mul_C_mul_posDef_iff (n := 1) (u := v) (v := u) hv hu).symm

lemma StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_two
    {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix 2 q p).PosDef :=
  ⟨StrictPrecSameDegree.bezoutMatrix_posDef_quadratic hp_pos hq_pos hp_deg hq_deg, fun h ↦
    have hp_rr : p ≠ 0 ∧ p.Splits :=
      bezoutMatrix.right_isRealRooted_of_posDef_two_of_natDegree_two hp_deg hq_deg.le h
    have hq_rr : q ≠ 0 ∧ q.Splits :=
      bezoutMatrix.left_isRealRooted_of_posDef_two_of_natDegree_two hp_deg.le hq_deg h
    (StrictPrecSameDegree.bezoutMatrix_posDef_iff_of_isRealRooted_quadratic
      hp_rr.2 hq_rr.2 hp_pos hq_pos hp_deg hq_deg).mpr h⟩

/--
Strict same-degree Bezoutian characterization.

The orientation is chosen so that `StrictPrecSameDegree p q` corresponds to
positive definiteness of `bezoutMatrix n q p`.
-/
theorem strictPrecSameDegree_iff_bezoutMatrix_posDef
    {p q : ℝ[X]} {n : ℕ}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n) :
    StrictPrecSameDegree p q ↔ (bezoutMatrix n q p).PosDef :=
  match n, hp_deg, hq_deg with
  | 0, hp_deg, hq_deg =>
    StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_zero
      hp_pos hq_pos hp_deg hq_deg
  | 1, hp_deg, hq_deg =>
    StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_one
      hp_pos hq_pos hp_deg hq_deg
  | 2, hp_deg, hq_deg =>
    StrictPrecSameDegree.bezoutMatrix_posDef_iff_natDegree_two
      hp_pos hq_pos hp_deg hq_deg
  | _n + 3, hp_deg, hq_deg =>
    ⟨StrictPrecSameDegree.bezoutMatrix_posDef_three_le
       hp_pos hq_pos hp_deg hq_deg,
      StrictPrecSameDegree.of_bezoutMatrix_posDef_three_le
       hp_pos hq_pos hp_deg hq_deg⟩

end RealRooted
