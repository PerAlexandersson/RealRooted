import RealRooted.SymmetricDecomposition.Decomposition

/-!
# Brändén--Solus Theorem 2.6

The proper-position equivalences, boundary analysis, and ordered-degree bridge
for the symmetric-decomposition real-rootedness theorem.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

lemma prec_of_prec0_of_ne_zero {f g : ℝ[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (h : Prec0 f g) :
    Prec f g := by
  rcases h with rfl | rfl | hprec <;> lia

private lemma natDegree_add_X_mul_ge_of_hasNonnegCoeffs
    {a b : ℝ[X]}
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0) :
    b.natDegree + 1 ≤ (a + X * b).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  have hcoeff_pos : 0 < (a + X * b).coeff (b.natDegree + 1) := by
    rw [Polynomial.coeff_add, Polynomial.coeff_X_mul]
    have ha_coeff_nonneg : 0 ≤ a.coeff (b.natDegree + 1) := ha_nonneg _
    have hb_top_pos : 0 < b.coeff b.natDegree := by
      simpa [HasPosLeadingCoeff] using hb_nonneg.pos_leadingCoeff hb0
    linarith
  grind

private lemma leadingCoeff_add_X_mul_eq_of_natDegree_le
    {a b : ℝ[X]}
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0) :
    (a + X * b).leadingCoeff = b.leadingCoeff := by
  have hXb_pos : HasPosLeadingCoeff (X * b) :=
    (hb_nonneg.pos_leadingCoeff hb0).X_mul
  have hdeg_lt : a.natDegree < (X * b).natDegree := by simp_all
  have hsum_deg : (a + X * b).natDegree = (X * b).natDegree :=
    natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hXb_pos
  have hXb_deg : (X * b).natDegree = b.natDegree + 1 := by simp_all
  have ha_top : a.coeff (b.natDegree + 1) = 0 := by
    have hdeg_top : a.natDegree < b.natDegree + 1 := by lia
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hdeg_top
  calc
    (a + X * b).leadingCoeff = (a + X * b).coeff (b.natDegree + 1) := by
      rw [Polynomial.leadingCoeff, hsum_deg, hXb_deg]
    _ = a.coeff (b.natDegree + 1) + (X * b).coeff (b.natDegree + 1) := by simp
    _ = b.coeff b.natDegree := by simp_all
    _ = b.leadingCoeff := by simp

private lemma natDegree_right_of_prec_to_sum
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0)
    (hbp : Prec b p) :
    b.natDegree + 1 = p.natDegree := by
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_hi : p.natDegree ≤ b.natDegree + 1 := by
    rcases hbp with ⟨hb_rr, hp_rr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
    have hss_len : ss.length = b.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hb_rr.2]
    have hrs_len : rs.length = p.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hp_rr.2]
    lia
  lia

/-- Converse branch for the Brändén--Solus decomposition theorem: if the right
component `b` already interlaces `p = a + X*b`, and the top degree of `p`
comes entirely from `X*b`, then subtracting that `X*b` term preserves the
left interlacing relation. -/
private theorem prec_b_component_of_prec_sum_of_leadingCoeff_eq
    {p a b : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (hbp : Prec b p)
    (hlc : p.leadingCoeff = b.leadingCoeff) :
    Prec b a := by
  have hp0 : p ≠ 0 := hbp.2.1.1
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hp_eq] using ha_nonneg.add hb_nonneg.X_mul
  have hdeg : b.natDegree + 1 = p.natDegree :=
    natDegree_right_of_prec_to_sum hp_eq ha_nonneg hb_nonneg hb0 hbp
  let c : ℝ := p.leadingCoeff⁻¹
  have hc_ne : c ≠ 0 :=
    inv_ne_zero (ne_of_gt (hp_nonneg.pos_leadingCoeff hp0))
  have hp_monic : (C c * p).Monic := by
    unfold c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hb_monic : (C c * b).Monic := by
    unfold c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hscaled : Prec (C c * b) (C c * p) :=
    prec_C_mul_right (prec_C_mul_left hbp hc_ne) hc_ne
  have hp_nonpos : ∀ r ∈ p.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hbp.2.1.2 hp_nonneg
  have hb_nonpos : ∀ r ∈ b.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hbp.1.2 hb_nonneg
  have hdeg_scaled : (C c * b).natDegree + 1 = (C c * p).natDegree := by
    rw [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_C_mul hc_ne, hdeg]
  have hprec0 : Prec0 (C c * b) (C c * p - X * (C c * b)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
      prec_sub_X_mul_right
        (f := C c * p) (g := C c * b)
        hscaled hp_monic hb_monic hdeg_scaled
        (by
          simp_all)
        (by
          simp_all)
  have hXC : C c * (X * b) = X * (C c * b) := by grind
  have hsub_eq : C c * p - X * (C c * b) = C c * a := by grind
  rw [hsub_eq] at hprec0
  have hCb0 : C c * b ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne) hb0
  have hCa0 : C c * a ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne) ha0
  have hscaled_prec : Prec (C c * b) (C c * a) :=
    prec_of_prec0_of_ne_zero hCb0 hCa0 hprec0
  have hback :
      Prec (C c⁻¹ * (C c * b)) (C c⁻¹ * (C c * a)) :=
    prec_C_mul_right
      (prec_C_mul_left hscaled_prec (inv_ne_zero hc_ne))
      (inv_ne_zero hc_ne)
  have hcancel_b : C c⁻¹ * (C c * b) = b := by
    calc
      C c⁻¹ * (C c * b) = C (c⁻¹ * c) * b := by grind
      _ = b := by simp_all
  have hcancel_a : C c⁻¹ * (C c * a) = a := by
    calc
      C c⁻¹ * (C c * a) = C (c⁻¹ * c) * a := by grind
      _ = a := by simp_all
  lia

theorem brandenSolusTheorem26_forward_of_prec_b_a {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hba : Prec b a) :
    Prec a p ∧ Prec b p ∧ Prec (IdTransform d p) p := by
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : IdTransform d p = a + b :=
    idTransform_eq_add_of_isIdDecomposition hd hid
  have hb_rr : (b ≠ 0 ∧ b.Splits) := hba.1
  have ha_rr : (a ≠ 0 ∧ a.Splits) := hba.2.1
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb_rr.1
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha_rr.1
  have hXb_nonneg : HasNonnegCoeffs (X * b) := hb_nonneg.X_mul
  have hXb_pos : HasPosLeadingCoeff (X * b) := hb_pos.X_mul
  have haxb : Prec a (X * b) := prec_mul_X_of_prec_of_nonneg hba hb_nonneg ha_nonneg
  have hp_right : Prec (a + X * b) (X * b) := by
    simpa using
      (prec_nonneg_combo_right haxb ha_pos hXb_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp) (by simp)
        (Or.inl (by simp)))
  have hp0 : p ≠ 0 := by simpa [hp_eq] using hp_right.1.1
  have hap : Prec a p := by
    have hprec0 : Prec0 a ([a, X * b].sum) := by
      refine prec0_sum_left_of_common_left_of_nonneg [a, X * b] a ?_ ?_
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact (prec_refl ha_rr.1 ha_rr.2).toPrec0
        · exact haxb.toPrec0
      · simp_all
    exact prec_of_prec0_of_ne_zero ha_rr.1 hp0 (by simp_all)
  have hbXb : Prec b (X * b) :=
    prec_mul_X_of_prec_of_nonneg (prec_refl hb_rr.1 hb_rr.2) hb_nonneg hb_nonneg
  have hbp : Prec b p := by
    have hprec0 : Prec0 b ([a, X * b].sum) := by
      refine prec0_sum_left_of_common_left_of_nonneg [a, X * b] b ?_ ?_
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hba.toPrec0
        · exact hbXb.toPrec0
      · simp_all
    exact prec_of_prec0_of_ne_zero hb_rr.1 hp0 (by simp_all)
  have hIda : Prec (a + b) a := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (prec_nonneg_combo_right hba hb_pos ha_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp) (by simp)
        (Or.inl (by simp)))
  have hIdp : Prec (IdTransform d p) p := by
    have hprec0 : Prec0 (∑ t ∈ (Finset.univ : Finset Bool), cond t b a) p := by
      refine prec0_finsetSum_right_of_nonneg (s := (Finset.univ : Finset Bool))
        (f := fun t => cond t b a) (h := p) ?_ ?_
      · intro t ht
        cases t <;> simp [hap.toPrec0, hbp.toPrec0]
      · lia
    have hId0 : IdTransform d p ≠ 0 := by simpa [hId_eq] using hIda.1.1
    exact prec_of_prec0_of_ne_zero hId0 hp0 (by
      simpa [hId_eq, add_comm, add_left_comm, add_assoc] using hprec0)
  lia

theorem brandenSolusTheorem26_third_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (Prec b a ↔ Prec b p) := by
  constructor
  · intro hba
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.1
  · intro hbp
    have hlc : p.leadingCoeff = b.leadingCoeff := by
      rw [hid.1]
      exact leadingCoeff_add_X_mul_eq_of_natDegree_le ha_le hb_nonneg hb0
    exact
      prec_b_component_of_prec_sum_of_leadingCoeff_eq
        hid.1 ha_nonneg hb_nonneg ha0 hb0 hbp hlc

private theorem allComboRealRooted_left_X_mul_component_of_prec_left
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (hap : Prec a p) :
    AllComboRealRooted a (X * b) := by
  have hall_ap : AllComboRealRooted a p := allComboRealRooted_of_prec hap
  intro α β
  have hrew :
      C α * a + C β * (X * b) =
        C (α - β) * a + C β * p := by
    grind
  simpa [hrew] using hall_ap (α - β) β

private theorem allComboRealRooted_left_X_mul_component_of_prec_right
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (hpxb : Prec p (X * b)) :
    AllComboRealRooted a (X * b) := by
  have hall_pXb : AllComboRealRooted p (X * b) := allComboRealRooted_of_prec hpxb
  intro α β
  have hrew :
      C α * a + C β * (X * b) =
        C α * p + C (β - α) * (X * b) := by
    grind
  simpa [hrew] using hall_pXb α (β - α)

private theorem prec_b_component_of_prec_left_of_natDegree_le
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb0 : b ≠ 0)
    (hap : Prec a p) :
    Prec b a := by
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_hi : p.natDegree ≤ a.natDegree + 1 :=
    hap.natDegree_le_succ
  have hp_deg : p.natDegree = b.natDegree + 1 := by lia
  have hab_eq : a.natDegree = b.natDegree := by lia
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
  have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
    ⟨mul_ne_zero X_ne_zero hb0, hall_aXb.right_splits⟩
  have hdeg_aXb : a.natDegree + 1 = (X * b).natDegree := by simp_all
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a :=
    prec_of_allComboRealRooted hap.1.1 hap.1.2 hXb_rr.1 hXb_rr.2 hall_aXb
      (Or.inl hdeg_aXb)
  have hprec_aXb : Prec a (X * b) :=
    prec_forward_of_orientation_of_succDegree hdeg_aXb.symm hprec_or
  exact prec_of_prec_mul_X_of_nonneg hprec_aXb hb_nonneg ha_nonneg

private theorem natDegree_X_mul_component_eq_or_succ_of_prec_left_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_top : a.natDegree = d)
    (hb0 : b ≠ 0)
    (hap : Prec a p) :
    (X * b).natDegree = d ∨ (X * b).natDegree + 1 = d := by
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
  have hXb0 : X * b ≠ 0 := mul_ne_zero X_ne_zero hb0
  have hXb_le_p : (X * b).natDegree ≤ p.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    have hcoeff_pos : 0 < p.coeff (X * b).natDegree := by
      rw [hp_eq, Polynomial.coeff_add]
      have ha_coeff_nonneg : 0 ≤ a.coeff (X * b).natDegree := ha_nonneg _
      have hXb_top_pos : 0 < (X * b).coeff (X * b).natDegree := by
        have hlead : 0 < (X * b).leadingCoeff :=
          (hb_nonneg.pos_leadingCoeff hb0).X_mul
        simp_all
      linarith
    grind
  have hXb_le_d : (X * b).natDegree ≤ d := le_trans hXb_le_p hd
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall_aXb hap.1.1 hXb0 with
    hdeg | hdeg | hdeg <;> lia

private lemma not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]}
    (hfix : IdTransform d p = p)
    (hdeg : p.natDegree = d)
    (hp_nonneg : HasNonnegCoeffs p)
    (hp0 : p ≠ 0) :
    ¬ p.IsRoot 0 := by
  intro hp_root0
  have hcoeff : p.coeff 0 = p.coeff d := by
    simpa [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using
      (congrArg (fun q => q.coeff 0) hfix).symm
  have htop : 0 < p.coeff d := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact hp_nonneg.pos_leadingCoeff hp0
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at hp_root0
  simp_all

private lemma exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
    {p : ℝ[X]}
    (hp_rr_ne : p ≠ 0) (hp_rr_splits : p.Splits)
    (hp_nonneg : HasNonnegCoeffs p)
    (hp0_root : ¬ p.IsRoot 0) :
    ∃ c : ℝ, (∀ s ∈ p.roots, s ≤ c) ∧ c < 0 := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  by_cases hrs_nil : rs = []
  · refine ⟨-1, ?_, by simp⟩
    intro s hs
    have hs' : s ∈ rs := by
      have : s ∈ (↑rs : Multiset ℝ) := by lia
      exact Multiset.mem_coe.mp this
    simp_all
  · refine ⟨rs.getLast hrs_nil, ?_, ?_⟩
    · intro s hs
      have hs' : s ∈ rs := by
        have : s ∈ (↑rs : Multiset ℝ) := by lia
        exact Multiset.mem_coe.mp this
      exact List.Pairwise.rel_getLast hrs_sorted hs'
    · have hc_root : p.IsRoot (rs.getLast hrs_nil) := by
        have hc_mem : rs.getLast hrs_nil ∈ rs := List.getLast_mem hrs_nil
        have : rs.getLast hrs_nil ∈ (↑rs : Multiset ℝ) := Multiset.mem_coe.mpr hc_mem
        simp_all
      have hc_nonpos : rs.getLast hrs_nil ≤ 0 :=
        roots_nonpos_of_nonneg_coeffs hp_rr_splits hp_nonneg (rs.getLast hrs_nil) <|
          (mem_roots hp_rr_ne).mpr hc_root
      grind

private theorem prec_b_component_of_prec_left_top_of_sameDegree
    {d : ℕ} {p a b : ℝ[X]}
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hXb_top : (X * b).natDegree = d)
    (hap : Prec a p) :
    Prec b a := by
  have hp_eq : p = a + X * b := hid.1
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
  have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
    ⟨mul_ne_zero X_ne_zero hb0, hall_aXb.right_splits⟩
  have hsame : a.natDegree = (X * b).natDegree := by lia
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a :=
    prec_of_allComboRealRooted hap.1.1 hap.1.2 hXb_rr.1 hXb_rr.2 hall_aXb
      (Or.inr hsame)
  have ha_not_root0 : ¬ a.IsRoot 0 :=
    not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
      hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      hap.1.1 hap.1.2 ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by simp
  have hprec_aXb : Prec a (X * b) :=
    PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
      (f := X * b) (g := a) (c := c) (r := 0)
      (by lia)
      hac_le hXb_root0 hc_lt0
  exact prec_of_prec_mul_X_of_nonneg hprec_aXb hb_nonneg ha_nonneg

private theorem prec_b_component_of_prec_left_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hap : Prec a p) :
    Prec b a := by
  have hp_eq : p = a + X * b := hid.1
  have hXb_case :
      (X * b).natDegree = d ∨ (X * b).natDegree + 1 = d :=
    natDegree_X_mul_component_eq_or_succ_of_prec_left_top
      hd hp_eq ha_nonneg hb_nonneg ha_top hb0 hap
  rcases hXb_case with hXb_top | hXb_gap
  · exact
      prec_b_component_of_prec_left_top_of_sameDegree
        hid ha_nonneg hb_nonneg ha0 hb0 ha_top hXb_top hap
  · exfalso
    have hall_aXb : AllComboRealRooted a (X * b) :=
      allComboRealRooted_left_X_mul_component_of_prec_left hp_eq hap
    have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
      ⟨mul_ne_zero X_ne_zero hb0, hall_aXb.right_splits⟩
    have hall_Xba : AllComboRealRooted (X * b) a := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_aXb β α
    have hprec_or : Prec (X * b) a ∨ Prec a (X * b) := by
      have hdeg : (X * b).natDegree + 1 = a.natDegree := by lia
      exact prec_of_allComboRealRooted hXb_rr.1 hXb_rr.2 hap.1.1 hap.1.2 hall_Xba (Or.inl hdeg)
    have ha_not_root0 : ¬ a.IsRoot 0 :=
      not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
        hid.2.2.2.1 ha_top ha_nonneg ha0
    obtain ⟨c, hac_le, hc_lt0⟩ :=
      exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
        hap.1.1 hap.1.2 ha_nonneg ha_not_root0
    have hXb_root0 : (X * b).IsRoot 0 := by simp
    have hbad : Prec a (X * b) :=
      PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
        (f := X * b) (g := a) (c := c) (r := 0)
        hprec_or hac_le hXb_root0 hc_lt0
    have hbound : a.natDegree ≤ (X * b).natDegree := hbad.natDegree_le
    lia

private theorem prec_b_component_of_prec_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hbp : Prec b p) :
    Prec b a := by
  have hp_eq : p = a + X * b := hid.1
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hp_eq] using ha_nonneg.add hb_nonneg.X_mul
  have hpxb : Prec p (X * b) := prec_mul_X_of_prec_of_nonneg hbp hb_nonneg hp_nonneg
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_prec_right hp_eq hpxb
  have ha_rr : (a ≠ 0 ∧ a.Splits) := ⟨ha0, hall_aXb.left_splits⟩
  have hp_deg : p.natDegree = d := by
    apply le_antisymm hd
    apply Polynomial.le_natDegree_of_ne_zero
    have hcoeff_pos : 0 < p.coeff d := by
      rw [hp_eq, Polynomial.coeff_add]
      have ha_top_pos : 0 < a.coeff d := by
        rw [← ha_top, Polynomial.coeff_natDegree]
        exact ha_nonneg.pos_leadingCoeff ha0
      have hXb_coeff_nonneg : 0 ≤ (X * b).coeff d :=
        hb_nonneg.X_mul d
      linarith
    grind
  have hbp_deg : b.natDegree + 1 = p.natDegree :=
    natDegree_right_of_prec_to_sum hp_eq ha_nonneg hb_nonneg hb0 hbp
  have hsame : a.natDegree = (X * b).natDegree := by simp_all
  have ha_not_root0 : ¬ a.IsRoot 0 :=
    not_isRoot_zero_of_IdTransform_fixed_top_of_hasNonnegCoeffs
      hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      ha_rr.1 ha_rr.2 ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by simp
  have hprec_or : Prec a (X * b) ∨ Prec (X * b) a :=
    prec_of_allComboRealRooted ha_rr.1 ha_rr.2 hpxb.2.1.1 hpxb.2.1.2 hall_aXb
      (Or.inr hsame)
  have hprec_aXb : Prec a (X * b) :=
    PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
      (f := X * b) (g := a) (c := c) (r := 0)
      (by lia)
      hac_le hXb_root0 hc_lt0
  exact prec_of_prec_mul_X_of_nonneg hprec_aXb hb_nonneg ha_nonneg

theorem brandenSolusTheorem26_first_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (Prec b a ↔ Prec a p) := by
  constructor
  · intro hba
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1
  · intro hap
    exact
      prec_b_component_of_prec_left_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hap

theorem brandenSolusTheorem26_forward_of_prec_a_p_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    Prec a p → Prec b p ∧ Prec (IdTransform d p) p := by
  intro hap
  have hba : Prec b a :=
    (brandenSolusTheorem26_first_equiv_of_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top).2 hap
  exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2

theorem brandenSolusTheorem26_second_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (Prec a p ↔ Prec b p) := by
  constructor
  · intro hap
    exact
      (brandenSolusTheorem26_forward_of_prec_a_p_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hap).1
  · intro hbp
    have hba : Prec b a :=
      prec_b_component_of_prec_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hbp
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1

theorem brandenSolusTheorem26_third_forward_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    Prec b p → Prec (IdTransform d p) p := by
  intro hbp
  have hba : Prec b a :=
    prec_b_component_of_prec_right_top
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hbp
  exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.2

private theorem prec_b_component_of_prec_Id_top_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1)
    (hIdp : Prec (IdTransform d p) p) :
    Prec b p := by
  let h : ℝ[X] := IdTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hp_eq] using ha_nonneg.add hb_nonneg.X_mul
  have hh_nonneg : HasNonnegCoeffs h := by
    rw [hId_eq]
    exact ha_nonneg.add hb_nonneg
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb0
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hb_succ : b.natDegree + 1 = d := by lia
  have hh_deg : h.natDegree = d := by
    rw [hId_eq]
    have hdeg_lt : b.natDegree < a.natDegree := by lia
    calc
      (a + b).natDegree = a.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt ha_pos
      _ = d := ha_top
  have hdeg_lt : b.natDegree < a.natDegree := by lia
  have hh_pos : HasPosLeadingCoeff h := by
    rw [hId_eq]
    exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt ha_pos
  have hp_split : p = h + t := by grind
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      grind
    simpa [hrew] using hall_hp (α - β) β
  have ht_ne : t ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, hall_ht.right_splits⟩
  have ht_pos : HasPosLeadingCoeff t := by
    dsimp [t]
    exact hasPosLeadingCoeff_X_sub_C_mul (r := (1 : ℝ)) hb_pos
  have hb_rr : (b ≠ 0 ∧ b.Splits) := by
    apply isRealRooted_of_dvd ht_rr.1 ht_rr.2 hb0
    refine ⟨X - C (1 : ℝ), ?_⟩
    grind
  have hh_nonpos : ∀ r ∈ h.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hIdp.1.2 hh_nonneg
  have hsame : h.natDegree = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    lia
  have hprec_or : Prec h t ∨ Prec t h :=
    prec_of_allComboRealRooted hIdp.1.1 hIdp.1.2 ht_rr.1 ht_rr.2 hall_ht
      (Or.inr hsame)
  have ht_root1 : t.IsRoot 1 := by
    dsimp [t]
    simp
  have hht : Prec h t :=
    PosComboRealRooted.prec_of_prec_or_revPrec_of_root_asymmetry
      (f := t) (g := h) (c := 0) (r := 1)
      (by lia)
      hh_nonpos ht_root1 (by simp)
  have ht_le_one : ∀ r ∈ t.roots, r ≤ 1 := by
    intro r hr
    dsimp [t] at hr
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0), roots_X_sub_C] at hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · simp_all
    · have hr0 : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hb_rr.2 hb_nonneg r hr
      linarith
  have hbh : Prec b h :=
    (interlaces_of_prec_sameDegree_rightmost_factor
      (f := h) (g := t) (q := b) (uR := 1)
      hht hsame ht_le_one (by lia)).toPrec
  have hb_le_one : ∀ r ∈ b.roots, r ≤ (1 : ℝ) := by
    intro r hr
    have hr0 : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hb_rr.2 hb_nonneg r hr
    linarith
  have hbt : Prec b t := by
    dsimp [t]
    exact prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le (1 : ℝ)
      (prec_refl hb_rr.1 hb_rr.2) rfl hb_pos hb_pos hb_le_one hb_le_one
  have hbp_sum : Prec b [h, t].sum := by
    refine prec_sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_ <;> simp_all
  simp_all

theorem brandenSolusTheorem26_third_converse_of_top_degree_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1) :
    Prec (IdTransform d p) p → Prec b p := by
  intro hIdp
  exact
    prec_b_component_of_prec_Id_top_of_right_top
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top hIdp

theorem brandenSolusTheorem26_third_equiv_of_top_degree_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1) :
    (Prec b p ↔ Prec (IdTransform d p) p) := by
  constructor
  · exact
      brandenSolusTheorem26_third_forward_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_third_converse_of_top_degree_of_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top

theorem brandenSolusTheorem26_third_converse_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    Prec (IdTransform d p) p → Prec b p := by
  intro hIdp
  let h : ℝ[X] := IdTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hh_nonneg : HasNonnegCoeffs h := by
    rw [hId_eq]
    exact ha_nonneg.add hb_nonneg
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_lt : b.natDegree < a.natDegree := by lia
  have hh_deg : h.natDegree = d := by
    rw [hId_eq]
    calc
      (a + b).natDegree = a.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt ha_pos
      _ = d := ha_top
  have hh_nonpos : ∀ r ∈ h.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hIdp.1.2 hh_nonneg
  have hp_split : p = h + t := by grind
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      grind
    simpa [hrew] using hall_hp (α - β) β
  have ht_ne : t ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, hall_ht.right_splits⟩
  have ht_root1 : t.IsRoot 1 := by
    dsimp [t]
    simp
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall_ht hIdp.1.1 ht_ne with
    hsame | htoo_big | hgap
  · have hb_top : b.natDegree = d - 1 := by
      dsimp [t] at hsame
      rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at hsame
      lia
    exact
      brandenSolusTheorem26_third_converse_of_top_degree_of_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top hIdp
  · dsimp [t] at htoo_big
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at htoo_big
    lia
  · have hall_th : AllComboRealRooted t h := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_ht β α
    have hprec_or : Prec t h ∨ Prec h t :=
      prec_of_allComboRealRooted ht_rr.1 ht_rr.2 hIdp.1.1 hIdp.1.2 hall_th
        (Or.inl hgap)
    have hnot_th : ¬ Prec t h := by
      intro hth
      have h1_le : (1 : ℝ) ≤ 0 :=
        roots_le_of_prec_right hth hh_nonpos 1 ((mem_roots hth.1.1).mpr ht_root1)
      linarith
    rcases hprec_or with hth | hht
    · lia
    · have hbound : h.natDegree ≤ t.natDegree := hht.natDegree_le
      lia

theorem brandenSolusTheorem26_third_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (Prec b p ↔ Prec (IdTransform d p) p) := by
  constructor
  · exact
      brandenSolusTheorem26_third_forward_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_third_converse_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top

theorem brandenSolusTheorem26_first_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb0 : b ≠ 0) :
    (Prec b a ↔ Prec a p) := by
  constructor
  · intro hba
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1
  · intro hap
    exact prec_b_component_of_prec_left_of_natDegree_le
      hid.1 ha_nonneg hb_nonneg ha_le hb0 hap

theorem brandenSolusTheorem26_second_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (Prec a p ↔ Prec b p) := by
  constructor
  · intro hap
    have hba : Prec b a :=
      (brandenSolusTheorem26_first_equiv_of_natDegree_le
        hd hid ha_nonneg hb_nonneg ha_le hb0).2 hap
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.1
  · intro hbp
    have hba : Prec b a :=
      (brandenSolusTheorem26_third_equiv_of_natDegree_le
        hd hid ha_nonneg hb_nonneg ha_le ha0 hb0).2 hbp
    exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).1

theorem hasNonnegCoeffs_pair_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs p ∧ HasNonnegCoeffs (IdTransform d p) := by
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hid.1] using ha_nonneg.add hb_nonneg.X_mul
  have hId_nonneg : HasNonnegCoeffs (IdTransform d p) := by
    rw [idTransform_eq_add_of_isIdDecomposition hd hid]
    exact ha_nonneg.add hb_nonneg
  lia

theorem hasNonnegCoeffs_fPolynomial_pair_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs (fPolynomial d p) ∧
      HasNonnegCoeffs (RdTransform d (fPolynomial d p)) := by
  rcases hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg with
    ⟨hp_nonneg, hId_nonneg⟩
  refine ⟨hasNonnegCoeffs_fPolynomial hp_nonneg, ?_⟩
  rw [RdTransform_fPolynomial]
  exact hasNonnegCoeffs_fPolynomial hId_nonneg

theorem hasNonnegCoeffs_pair_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hrd : IsRdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs p ∧ HasNonnegCoeffs (RdTransform d p) := by
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hrd.1] using ha_nonneg.add hb_nonneg.X_mul
  have hR_nonneg : HasNonnegCoeffs (RdTransform d p) := by
    rw [rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition hd hrd]
    exact ha_nonneg.add (hasNonnegCoeffs_X_add_one.mul hb_nonneg)
  lia

theorem hasNonnegCoeffs_transformed_components_of_isIdDecomposition {d : ℕ} {a b : ℝ[X]}
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs (fPolynomial d a) ∧ HasNonnegCoeffs (fPolynomial (d - 1) b) :=
  ⟨hasNonnegCoeffs_fPolynomial ha_nonneg, hasNonnegCoeffs_fPolynomial hb_nonneg⟩

lemma prec_iff_prec_mul_X_add_one_both {f g : ℝ[X]} :
    Prec ((X + 1) * f) ((X + 1) * g) ↔ Prec f g := by
  constructor
  · intro h
    have h' : Prec ((X - C (-1)) * f) ((X - C (-1)) * g) := by simp_all
    exact prec_of_prec_mul_X_sub_C_both (-1) h'
  · intro h
    have h' : Prec ((X - C (-1)) * f) ((X - C (-1)) * g) :=
      prec_mul_X_sub_C_both (-1) h
    simp_all

lemma prec_iff_prec_mul_X_add_one_pow_both {n : ℕ} {f g : ℝ[X]} :
    Prec ((X + 1) ^ n * f) ((X + 1) ^ n * g) ↔ Prec f g := by
  induction n with
  | zero =>
      lia
  | succ n ih =>
      have hstep :
          Prec ((X + 1) * ((X + 1) ^ n * f)) ((X + 1) * ((X + 1) ^ n * g)) ↔
            Prec ((X + 1) ^ n * f) ((X + 1) ^ n * g) :=
        prec_iff_prec_mul_X_add_one_both
      grind

/-- Reduced transport target: it is enough to treat the minimal ambient degree
`max u.natDegree v.natDegree`, since larger ambient degrees only add a common
power of `X + 1` to both transformed polynomials. -/
def precFPolynomialTransportMinimalStatement : Prop :=
  ∀ {d : ℕ} {u v : ℝ[X]},
    d = max u.natDegree v.natDegree →
    HasNonnegCoeffs u →
    HasNonnegCoeffs v →
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v)

/-- Honest missing transport problem behind Brändén--Solus Theorem 2.6:
the `f`-polynomial transform should preserve the oriented interlacing relation
on nonnegative-coefficient pairs of degree at most `d`. -/
def precFPolynomialTransportStatement : Prop :=
  ∀ {d : ℕ} {u v : ℝ[X]},
    u.natDegree ≤ d →
    v.natDegree ≤ d →
    HasNonnegCoeffs u →
    HasNonnegCoeffs v →
    (Prec (fPolynomial d u) (fPolynomial d v) ↔ Prec u v)

theorem precFPolynomialTransportMinimal : precFPolynomialTransportMinimalStatement := by
  intro d u v hd hu_nonneg hv_nonneg
  constructor
  · intro h
    have hud : u.natDegree ≤ d := by simp_all
    have hvd : v.natDegree ≤ d := by simp_all
    have hu_rr : (u ≠ 0 ∧ u.Splits) :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hud h.1.1 h.1.2 hu_nonneg
    have hv_rr : (v ≠ 0 ∧ v.Splits) :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hvd h.2.1.1 h.2.1.2 hv_nonneg
    exact prec_of_prec_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
      hd hu_rr.1 hu_rr.2 hv_rr.1 hv_rr.2 h hu_nonneg hv_nonneg
  · intro h
    exact prec_fPolynomial_of_prec_of_hasNonnegCoeffs_of_minimal hd h hu_nonneg hv_nonneg

theorem precFPolynomialTransport_of_minimal
    (hminimal : precFPolynomialTransportMinimalStatement) :
    precFPolynomialTransportStatement := by
  intro d u v hud hvd hu_nonneg hv_nonneg
  let m := max u.natDegree v.natDegree
  have hum : u.natDegree ≤ m := le_max_left _ _
  have hvm : v.natDegree ≤ m := le_max_right _ _
  have hmd : m ≤ d := max_le hud hvd
  have hu_pad : fPolynomial d u = (X + 1) ^ (d - m) * fPolynomial m u := by
    simpa [m] using fPolynomial_pad_by_X_add_one_pow hum hmd
  have hv_pad : fPolynomial d v = (X + 1) ^ (d - m) * fPolynomial m v := by
    simpa [m] using fPolynomial_pad_by_X_add_one_pow hvm hmd
  calc
    Prec (fPolynomial d u) (fPolynomial d v)
        ↔ Prec ((X + 1) ^ (d - m) * fPolynomial m u)
          ((X + 1) ^ (d - m) * fPolynomial m v) := by lia
    _ ↔ Prec (fPolynomial m u) (fPolynomial m v) :=
          prec_iff_prec_mul_X_add_one_pow_both
    _ ↔ Prec u v := hminimal (d := m) rfl hu_nonneg hv_nonneg

theorem precFPolynomialTransport : precFPolynomialTransportStatement :=
  precFPolynomialTransport_of_minimal precFPolynomialTransportMinimal

theorem brandenSolusTheorem26_last_equiv_of_precFPolynomialTransport
    (htransport : precFPolynomialTransportStatement)
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  rcases hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg with
    ⟨hp_nonneg, hId_nonneg⟩
  rw [RdTransform_fPolynomial]
  exact (htransport
    (u := IdTransform d p) (v := p)
    (IdTransform_natDegree_le hd) hd hId_nonneg hp_nonneg).symm

theorem brandenSolusTheorem26_last_equiv
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) :=
  brandenSolusTheorem26_last_equiv_of_precFPolynomialTransport
    precFPolynomialTransport hd hid ha_nonneg hb_nonneg

private theorem brandenSolusTheorem26_descend_of_lt_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hd2 : 2 ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_lt : a.natDegree < d)
    (hb_lt : b.natDegree < d - 1)
    (hprev :
      ∀ {q a' b' : ℝ[X]},
        q.natDegree ≤ d - 2 →
        IsIdDecomposition (d - 2) q a' b' →
        HasNonnegCoeffs a' →
        HasNonnegCoeffs b' →
        a' ≠ 0 →
        b' ≠ 0 →
        (Prec b' a' ↔ Prec a' q) ∧
        (Prec a' q ↔ Prec b' q) ∧
        (Prec b' q ↔ Prec (IdTransform (d - 2) q) q) ∧
        (Prec (IdTransform (d - 2) q) q ↔
          Prec (RdTransform (d - 2) (fPolynomial (d - 2) q)) (fPolynomial (d - 2) q))) :
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  rcases isIdDecomposition_descend_of_lt_top hd2 hid ha_lt hb_lt with
    ⟨a', b', haX, hbX, hpX, hid'⟩
  let q : ℝ[X] := a' + X * b'
  have hidq : IsIdDecomposition (d - 2) q a' b' := by lia
  have ha'0 : a' ≠ 0 := by simp_all
  have hb'0 : b' ≠ 0 := by simp_all
  have ha'_nonneg : HasNonnegCoeffs a' :=
    hasNonnegCoeffs_of_eq_X_mul ha_nonneg haX
  have hb'_nonneg : HasNonnegCoeffs b' :=
    hasNonnegCoeffs_of_eq_X_mul hb_nonneg hbX
  have hXb'deg : (X * b').natDegree ≤ d - 2 := by lia
  have hqdeg : q.natDegree ≤ d - 2 := by
    simpa [q] using Polynomial.natDegree_add_le_of_le hidq.2.1 hXb'deg
  have hpair_nonneg :=
    hasNonnegCoeffs_pair_of_isIdDecomposition hqdeg hidq ha'_nonneg hb'_nonneg
  have hq_nonneg : HasNonnegCoeffs q := hpair_nonneg.1
  have hIdq_nonneg : HasNonnegCoeffs (IdTransform (d - 2) q) := hpair_nonneg.2
  have hpX' : p = X * q := by lia
  have hIdX : IdTransform d p = X * IdTransform (d - 2) q := by
    calc
      IdTransform d p = IdTransform d (X * q) := by lia
      _ = X * IdTransform (d - 2) q :=
        IdTransform_X_mul_of_natDegree_le_two_pred hd2 hqdeg
  have hsmall := hprev hqdeg hidq ha'_nonneg hb'_nonneg ha'0 hb'0
  rcases hsmall with ⟨hfirst_small, hsecond_small, hthird_small, -⟩
  have hba_transport : Prec b a ↔ Prec b' a' := by
    calc
      Prec b a ↔ Prec (X * b') (X * a') := by lia
      _ ↔ Prec b' a' :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hb'_nonneg ha'_nonneg).symm
  have hap_transport : Prec a p ↔ Prec a' q := by
    calc
      Prec a p ↔ Prec (X * a') (X * q) := by lia
      _ ↔ Prec a' q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs ha'_nonneg hq_nonneg).symm
  have hbp_transport : Prec b p ↔ Prec b' q := by
    calc
      Prec b p ↔ Prec (X * b') (X * q) := by lia
      _ ↔ Prec b' q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hb'_nonneg hq_nonneg).symm
  have hIdp_transport : Prec (IdTransform d p) p ↔ Prec (IdTransform (d - 2) q) q := by
    calc
      Prec (IdTransform d p) p ↔ Prec (X * IdTransform (d - 2) q) (X * q) := by lia
      _ ↔ Prec (IdTransform (d - 2) q) q :=
        (prec_iff_prec_mul_X_both_of_hasNonnegCoeffs hIdq_nonneg hq_nonneg).symm
  refine ⟨?_, ?_, ?_, brandenSolusTheorem26_last_equiv hd hid ha_nonneg hb_nonneg⟩ <;> lia

/-- Naive fully strict translation of Brändén--Solus Theorem 2.6 into the
current `Prec` API.

This exact formulation is false: our `Prec` predicate is reflexive on
real-rooted polynomials and excludes the zero polynomial, so degenerate
decompositions such as `p = 1`, `a = 1`, `b = 0` break the first equivalence.
We keep this definition only so that the counterexample is recorded explicitly
in the library. -/
def brandenSolusTheorem26NaiveStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))

/-- The naive fully strict `Prec` formulation of Brändén--Solus Theorem 2.6 is
false. The counterexample is the degree-zero decomposition `1 = 1 + X * 0`. -/
theorem not_brandenSolusTheorem26NaiveStatement :
    ¬ brandenSolusTheorem26NaiveStatement := by
  intro h
  have hcase := h (d := 0) (p := (1 : ℝ[X])) (a := (1 : ℝ[X])) (b := 0)
    (by simp)
    (by
      refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [IdTransform])
    hasNonnegCoeffs_one
    hasNonnegCoeffs_zero
  rcases hcase with ⟨hba_iff_hap, -, -, -⟩
  have happ : Prec (1 : ℝ[X]) (1 : ℝ[X]) :=
    prec_refl (by simp) (by simp)
  have hnot : ¬ Prec (0 : ℝ[X]) (1 : ℝ[X]) :=
    fun h0 => h0.1.1 rfl
  lia

/-- Honest nondegenerate `Prec` target for Brändén--Solus Theorem 2.6.

The extra assumptions `a ≠ 0` and `b ≠ 0` remove the zero-polynomial edge
cases where the paper's strict interlacing language and the current Lean
predicate `Prec` diverge. -/
def brandenSolusTheorem26Statement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))

/-- Reduced frontier for Brändén--Solus Theorem 2.6: after the degree-ordered
and below-top recursive branches, the only genuinely new case is when the
left `I_d`-component occupies the full ambient degree. -/
def brandenSolusTheorem26TopDegreeBoundaryStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    a.natDegree = d →
    (Prec b a ↔ Prec a p) ∧
    (Prec a p ↔ Prec b p) ∧
    (Prec b p ↔ Prec (IdTransform d p) p) ∧
    (Prec (IdTransform d p) p ↔
      Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))

/-- Remaining ordered-degree bridge in the already-controlled branch
`a.natDegree ≤ b.natDegree`: upgrading the proved equivalence
`Prec b a ↔ Prec b p` to the desired `Prec b p ↔ Prec (IdTransform d p) p`. -/
def brandenSolusTheorem26OrderedBridgeStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    a.natDegree ≤ b.natDegree →
    (Prec b p ↔ Prec (IdTransform d p) p)

/-- In the ordered-degree branch `a.natDegree ≤ b.natDegree`, the forward half
of the remaining bridge is already available: once `b` interlaces `p`, the
existing component theorem recovers `b ≺ a`, and the forward Brändén--Solus
implication then yields `IdTransform d p ≺ p`. -/
theorem brandenSolusTheorem26_ordered_bridge_forward_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    Prec b p → Prec (IdTransform d p) p := by
  intro hbp
  have hba : Prec b a :=
    (brandenSolusTheorem26_third_equiv_of_natDegree_le
      hd hid ha_nonneg hb_nonneg ha_le ha0 hb0).2 hbp
  exact (brandenSolusTheorem26_forward_of_prec_b_a hd hid ha_nonneg hb_nonneg hba).2.2

/-- Ordered-degree converse bridge: if `a.natDegree ≤ b.natDegree` and
`IdTransform d p ≺ p`, then already `b ≺ p`.

The proof rewrites `p` as `IdTransform d p + (X - 1) * b`, extracts
`b ≺ IdTransform d p` from the shifted pair via the same-degree Obreschkoff
converse, and then sums back to `b ≺ p`. -/
theorem brandenSolusTheorem26_ordered_bridge_converse_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_le : a.natDegree ≤ b.natDegree) :
    Prec (IdTransform d p) p → Prec b p := by
  intro hIdp
  let h : ℝ[X] := IdTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hpair_nonneg := hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg
  have hp_nonneg : HasNonnegCoeffs p := hpair_nonneg.1
  have hh_nonneg : HasNonnegCoeffs h := by lia
  have hh_rr : (h ≠ 0 ∧ h.Splits) := by simpa [h] using hIdp.1
  have hp_rr : (p ≠ 0 ∧ p.Splits) := hIdp.2.1
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb0
  have hh_deg : h.natDegree = b.natDegree := by
    rw [hId_eq]
    by_cases hdeg_eq : a.natDegree = b.natDegree
    · calc
        (a + b).natDegree = a.natDegree :=
          natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq ha_pos hb_pos
        _ = b.natDegree := hdeg_eq
    · have hdeg_lt : a.natDegree < b.natDegree := lt_of_le_of_ne ha_le hdeg_eq
      exact natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hb_pos
  have hh_pos : HasPosLeadingCoeff h := by
    rw [hId_eq]
    by_cases hdeg_eq : a.natDegree = b.natDegree
    · exact hasPosLeadingCoeff_add_of_same_natDegree hdeg_eq ha_pos hb_pos
    · exact hasPosLeadingCoeff_add_of_natDegree_lt_right (lt_of_le_of_ne ha_le hdeg_eq) hb_pos
  have ht_ne : t ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_pos : HasPosLeadingCoeff t := by
    dsimp [t]
    exact hasPosLeadingCoeff_X_sub_C_mul (r := (1 : ℝ)) hb_pos
  have hp_split : p = h + t := by grind
  have hall_hp : AllComboRealRooted h p := allComboRealRooted_of_prec hIdp
  have hall_ht : AllComboRealRooted h t := by
    intro α β
    have hrew :
        C α * h + C β * t =
          C (α - β) * h + C β * p := by
      grind
    simpa [hrew] using hall_hp (α - β) β
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, hall_ht.right_splits⟩
  have hb_rr : (b ≠ 0 ∧ b.Splits) := by
    apply isRealRooted_of_dvd ht_rr.1 ht_rr.2 hb0
    refine ⟨X - C (1 : ℝ), ?_⟩
    grind
  have hb_le : ∀ s ∈ b.roots, s ≤ (1 : ℝ) := by
    intro s hs
    have hs0 := roots_nonpos_of_nonneg_coeffs hb_rr.2 hb_nonneg s hs
    linarith
  have hh_le : ∀ s ∈ h.roots, s ≤ (1 : ℝ) := by
    intro s hs
    have hs0 := roots_nonpos_of_nonneg_coeffs hh_rr.2 hh_nonneg s hs
    linarith
  have ht_deg : h.natDegree + 1 = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    lia
  have hht_or : Prec h t ∨ Prec t h :=
    prec_of_allComboRealRooted hh_rr.1 hh_rr.2 ht_rr.1 ht_rr.2 hall_ht
      (Or.inl ht_deg)
  have hht : Prec h t :=
    prec_forward_of_orientation_of_succDegree ht_deg.symm hht_or
  have hbh : Prec b h :=
    prec_of_prec_mul_X_sub_C_of_sameDegree_of_roots_le (1 : ℝ)
      hht hh_deg.symm hb_pos hh_pos hb_le hh_le
  have hbt : Prec b t :=
    prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le (1 : ℝ)
      (prec_refl hb_rr.1 hb_rr.2) rfl hb_pos hb_pos hb_le hb_le
  have hbp_sum : Prec b [h, t].sum := by
    refine prec_sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_ <;> simp_all
  simp_all

/-- The ordered-degree converse bridge, packaged as a standalone statement so it
can still be referenced in reduction theorems. This is now proved below. -/
def brandenSolusTheorem26OrderedBridgeConverseStatement : Prop :=
  ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    a ≠ 0 →
    b ≠ 0 →
    a.natDegree ≤ b.natDegree →
    (Prec (IdTransform d p) p → Prec b p)

/-- The bidirectional ordered-degree bridge reduces to its converse, since the
forward implication is already available from the current library. -/
theorem brandenSolusTheorem26OrderedBridge_of_converse
    (hconverse : brandenSolusTheorem26OrderedBridgeConverseStatement) :
    brandenSolusTheorem26OrderedBridgeStatement := by
  intro d p a b hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le
  constructor
  · exact brandenSolusTheorem26_ordered_bridge_forward_of_natDegree_le
      hd hid ha_nonneg hb_nonneg ha_le ha0 hb0
  · exact hconverse hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le

theorem brandenSolusTheorem26OrderedBridgeConverse :
    brandenSolusTheorem26OrderedBridgeConverseStatement := by
  intro d p a b hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le
  exact brandenSolusTheorem26_ordered_bridge_converse_of_natDegree_le
    hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le

/-- The full nondegenerate Brändén--Solus theorem reduces to the single
top-degree boundary case `a.natDegree = d`, together with the still-missing
ordered-degree bridge `Prec b p ↔ Prec (IdTransform d p) p`. The other
branches are already handled by the degree-ordered lemmas and the recursive
common-`X` descent. -/
theorem brandenSolusTheorem26_of_top_degree_boundary
    (hordered : brandenSolusTheorem26OrderedBridgeStatement)
    (hboundary : brandenSolusTheorem26TopDegreeBoundaryStatement) :
    brandenSolusTheorem26Statement := by
  let P : ℕ → Prop := fun d =>
    ∀ (p a b : ℝ[X]),
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      (Prec b a ↔ Prec a p) ∧
      (Prec a p ↔ Prec b p) ∧
      (Prec b p ↔ Prec (IdTransform d p) p) ∧
      (Prec (IdTransform d p) p ↔
        Prec (RdTransform d (fPolynomial d p)) (fPolynomial d p))
  have hmain : ∀ d, P d := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih p a b hd hid ha_nonneg hb_nonneg ha0 hb0
    have ha_deg : a.natDegree ≤ d := hid.2.1
    have hb_deg : b.natDegree ≤ d - 1 := hid.2.2.1
    by_cases ha_le : a.natDegree ≤ b.natDegree
    · refine ⟨?_, ?_, ?_, brandenSolusTheorem26_last_equiv hd hid ha_nonneg hb_nonneg⟩
      · exact brandenSolusTheorem26_first_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le hb0
      · exact brandenSolusTheorem26_second_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le ha0 hb0
      · exact hordered hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le
    · by_cases ha_top : a.natDegree = d
      · exact hboundary hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
      · have ha_lt : a.natDegree < d := lt_of_le_of_ne ha_deg ha_top
        have hb_lt : b.natDegree < d - 1 := by lia
        have hd2 : 2 ≤ d := by lia
        have hprev :
            ∀ {q a' b' : ℝ[X]},
              q.natDegree ≤ d - 2 →
              IsIdDecomposition (d - 2) q a' b' →
              HasNonnegCoeffs a' →
              HasNonnegCoeffs b' →
              a' ≠ 0 →
              b' ≠ 0 →
              (Prec b' a' ↔ Prec a' q) ∧
              (Prec a' q ↔ Prec b' q) ∧
              (Prec b' q ↔ Prec (IdTransform (d - 2) q) q) ∧
              (Prec (IdTransform (d - 2) q) q ↔
                Prec (RdTransform (d - 2) (fPolynomial (d - 2) q)) (fPolynomial (d - 2) q)) := by
          grind
        exact brandenSolusTheorem26_descend_of_lt_top
          hd hd2 hid ha_nonneg hb_nonneg ha0 hb0 ha_lt hb_lt hprev
  simpa [brandenSolusTheorem26Statement, P] using hmain

/-- Final wrapper in its sharper form: after packaging the already-proved
forward ordered-degree implication, the only remaining abstract inputs are the
top-degree boundary case and the converse half of the ordered bridge. -/
theorem brandenSolusTheorem26_of_ordered_bridge_converse_and_top_degree_boundary
    (hconverse : brandenSolusTheorem26OrderedBridgeConverseStatement)
    (hboundary : brandenSolusTheorem26TopDegreeBoundaryStatement) :
    brandenSolusTheorem26Statement :=
  brandenSolusTheorem26_of_top_degree_boundary
    (brandenSolusTheorem26OrderedBridge_of_converse hconverse)
    hboundary

/-- With the ordered-degree bridge now fully formalized, the only remaining
abstract input for Brändén--Solus Theorem 2.6 is the top-degree boundary case
`a.natDegree = d`. -/
theorem brandenSolusTheorem26_of_top_degree_boundary_only
    (hboundary : brandenSolusTheorem26TopDegreeBoundaryStatement) :
    brandenSolusTheorem26Statement :=
  brandenSolusTheorem26_of_ordered_bridge_converse_and_top_degree_boundary
    brandenSolusTheorem26OrderedBridgeConverse
    hboundary

theorem brandenSolusTheorem26TopDegreeBoundary :
    brandenSolusTheorem26TopDegreeBoundaryStatement := by
  intro d p a b hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      brandenSolusTheorem26_first_equiv_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_second_equiv_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact
      brandenSolusTheorem26_third_equiv_of_top_degree
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact brandenSolusTheorem26_last_equiv hd hid ha_nonneg hb_nonneg

theorem brandenSolusTheorem26 :
    brandenSolusTheorem26Statement :=
  brandenSolusTheorem26_of_top_degree_boundary_only
    brandenSolusTheorem26TopDegreeBoundary

end RealRooted
