import RealRooted.SymmetricDecomposition.Decomposition

/-!
# Brändén--Solus Theorem 2.6

The interlacing equivalences, boundary analysis, and ordered-degree bridge
for the symmetric-decomposition real-rootedness theorem.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

private lemma natDegree_add_X_mul_ge_of_hasNonnegCoeffs
    {a b : ℝ[X]}
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0) :
    b.natDegree + 1 ≤ (a + X * b).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  rw [Polynomial.coeff_add, Polynomial.coeff_X_mul]
  exact ne_of_gt <| add_pos_of_nonneg_of_pos (ha_nonneg _) <| by
    simpa [HasPosLeadingCoeff] using hb_nonneg.pos_leadingCoeff hb0

private lemma leadingCoeff_add_X_mul_eq_of_natDegree_le
    {a b : ℝ[X]}
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb0 : b ≠ 0) :
    (a + X * b).leadingCoeff = b.leadingCoeff := by
  have hdeg_lt : a.natDegree < (X * b).natDegree := by
    rw [natDegree_mul X_ne_zero hb0, natDegree_X]
    lia
  rw [Polynomial.leadingCoeff_add_of_degree_lt (Polynomial.degree_lt_degree hdeg_lt)]
  simp

private lemma natDegree_right_of_strictInterl_to_sum
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hb0 : b ≠ 0)
    (hbp : StrictInterl b p) :
    b.natDegree + 1 = p.natDegree := by
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_hi : p.natDegree ≤ b.natDegree + 1 := hbp.natDegree_le_succ
  lia

/-- Converse branch for the Brändén--Solus decomposition theorem: if the right
component `b` already interlaces `p = a + X*b`, and the top degree of `p`
comes entirely from `X*b`, then subtracting that `X*b` term preserves the
left interlacing relation. -/
private theorem strictInterl_b_component_of_strictInterl_sum_of_leadingCoeff_eq
    {p a b : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (hbp : StrictInterl b p)
    (hlc : p.leadingCoeff = b.leadingCoeff) :
    StrictInterl b a := by
  have hp0 : p ≠ 0 := hbp.2.1.1
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hp_eq] using ha_nonneg.add hb_nonneg.X_mul
  have hdeg : b.natDegree + 1 = p.natDegree :=
    natDegree_right_of_strictInterl_to_sum hp_eq ha_nonneg hb_nonneg hb0 hbp
  let c : ℝ := p.leadingCoeff⁻¹
  have hc_ne : c ≠ 0 := inv_ne_zero (ne_of_gt (hp_nonneg.pos_leadingCoeff hp0))
  have hlc_ne : p.leadingCoeff ≠ 0 := ne_of_gt (hp_nonneg.pos_leadingCoeff hp0)
  have hp_monic : (C c * p).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp [c, hlc_ne]
  have hblc_ne : b.leadingCoeff ≠ 0 := by simpa [hlc] using hlc_ne
  have hb_monic : (C c * b).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp [c, hlc, hblc_ne]
  have hscaled : StrictInterl (C c * b) (C c * p) :=
    StrictInterl.C_mul_right (StrictInterl.C_mul_left hbp hc_ne) hc_ne
  have hp_nonpos : ∀ r ∈ p.roots, r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hp_nonneg
  have hb_nonpos : ∀ r ∈ b.roots, r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hb_nonneg
  have hdeg_scaled : (C c * b).natDegree + 1 = (C c * p).natDegree := by
    rw [Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_C_mul hc_ne, hdeg]
  have hinterl : Interl (C c * b) (C c * p - X * (C c * b)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
      strictInterl_sub_X_mul_right
        (f := C c * p) (g := C c * b)
        hscaled hp_monic hb_monic hdeg_scaled
        (by simp_all) (by simp_all)
  have hsub_eq : C c * p - X * (C c * b) = C c * a := by grind
  rw [hsub_eq] at hinterl
  have hscaled_strictInterl : StrictInterl (C c * b) (C c * a) :=
    hinterl.toStrictInterl_of_ne
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne) hb0)
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne) ha0)
  have hback :
      StrictInterl (C c⁻¹ * (C c * b)) (C c⁻¹ * (C c * a)) :=
    StrictInterl.C_mul_right
      (StrictInterl.C_mul_left hscaled_strictInterl (inv_ne_zero hc_ne))
      (inv_ne_zero hc_ne)
  simpa [← mul_assoc, ← map_mul, hc_ne] using hback

theorem BrandenSolus.forward_of_strictInterl_b_a {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (hba : StrictInterl b a) :
    StrictInterl a p ∧ StrictInterl b p ∧ StrictInterl (idTransform d p) p := by
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : idTransform d p = a + b :=
    idTransform_eq_add_of_isIdDecomposition hd hid
  have hb_rr : (b ≠ 0 ∧ b.Splits) := hba.1
  have ha_rr : (a ≠ 0 ∧ a.Splits) := hba.2.1
  have hb_pos : HasPosLeadingCoeff b := hb_nonneg.pos_leadingCoeff hb_rr.1
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha_rr.1
  have hXb_nonneg : HasNonnegCoeffs (X * b) := hb_nonneg.X_mul
  have hXb_pos : HasPosLeadingCoeff (X * b) := hb_pos.X_mul
  have haxb : StrictInterl a (X * b) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hba hb_nonneg ha_nonneg
  have hp_right : StrictInterl (a + X * b) (X * b) := by
    simpa using
      (haxb.nonneg_combo_right ha_pos hXb_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp) (by simp)
        (Or.inl (by simp)))
  have hp0 : p ≠ 0 := by simpa [hp_eq] using hp_right.1.1
  have hap : StrictInterl a p := by
    have hinterl : Interl a ([a, X * b].sum) := by
      refine Interl.sum_left_of_common_left_of_nonneg [a, X * b] a ?_ ?_
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Interl.refl fun _ ↦ ha_rr.2
        · exact haxb.toInterl
      · simp_all
    exact (show Interl a p by simp_all).toStrictInterl_of_ne ha_rr.1 hp0
  have hbXb : StrictInterl b (X * b) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg
      (StrictInterl.refl hb_rr.1 hb_rr.2) hb_nonneg hb_nonneg
  have hbp : StrictInterl b p := by
    have hinterl : Interl b ([a, X * b].sum) := by
      refine Interl.sum_left_of_common_left_of_nonneg [a, X * b] b ?_ ?_
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hba.toInterl
        · exact hbXb.toInterl
      · simp_all
    exact (show Interl b p by simp_all).toStrictInterl_of_ne hb_rr.1 hp0
  have hIda : StrictInterl (a + b) a := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (hba.nonneg_combo_right hb_pos ha_pos
        (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp) (by simp)
        (Or.inl (by simp)))
  have hIdp : StrictInterl (idTransform d p) p := by
    have hinterl : Interl (∑ t ∈ (Finset.univ : Finset Bool), cond t b a) p := by
      refine Interl.finsetSum_right_of_nonneg (s := (Finset.univ : Finset Bool))
        (f := fun t => cond t b a) (h := p) ?_ ?_
      · intro t ht
        cases t <;> simp [hap.toInterl, hbp.toInterl]
      · lia
    have hId0 : idTransform d p ≠ 0 := by simpa [hId_eq] using hIda.1.1
    exact (by
      simpa [hId_eq, add_comm, add_left_comm, add_assoc] using hinterl :
        Interl (idTransform d p) p).toStrictInterl_of_ne hId0 hp0
  lia

theorem BrandenSolus.third_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (StrictInterl b a ↔ StrictInterl b p) := by
  constructor
  · exact fun hba ↦
      (BrandenSolus.forward_of_strictInterl_b_a hd hid ha_nonneg hb_nonneg hba).2.1
  · intro hbp
    have hlc : p.leadingCoeff = b.leadingCoeff := by
      rw [hid.1]
      exact leadingCoeff_add_X_mul_eq_of_natDegree_le ha_le hb0
    exact
      strictInterl_b_component_of_strictInterl_sum_of_leadingCoeff_eq
        hid.1 ha_nonneg hb_nonneg ha0 hb0 hbp hlc

private theorem allComboRealRooted_addend_of_strictInterl_left
    {a t p : ℝ[X]}
    (hp_eq : p = a + t)
    (hap : StrictInterl a p) :
    AllComboRealRooted a t := by
  have hall_ap : AllComboRealRooted a p := allComboRealRooted_of_strictInterl hap
  intro α β
  have hrew :
      C α * a + C β * t =
        C (α - β) * a + C β * p := by
    grind
  simpa [hrew] using hall_ap (α - β) β

private theorem allComboRealRooted_left_X_mul_component_of_strictInterl_right
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (hpxb : StrictInterl p (X * b)) :
    AllComboRealRooted a (X * b) := by
  have hall_pXb : AllComboRealRooted p (X * b) := allComboRealRooted_of_strictInterl hpxb
  intro α β
  have hrew :
      C α * a + C β * (X * b) =
        C α * p + C (β - α) * (X * b) := by
    grind
  simpa [hrew] using hall_pXb α (β - α)

private theorem strictInterl_b_component_of_strictInterl_left_of_natDegree_le
    {a b p : ℝ[X]}
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb0 : b ≠ 0)
    (hap : StrictInterl a p) :
    StrictInterl b a := by
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_hi : p.natDegree ≤ a.natDegree + 1 :=
    hap.natDegree_le_succ
  have hp_deg : p.natDegree = b.natDegree + 1 := by lia
  have hab_eq : a.natDegree = b.natDegree := by lia
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_addend_of_strictInterl_left hp_eq hap
  have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
    ⟨mul_ne_zero X_ne_zero hb0, hall_aXb.right_splits⟩
  have hdeg_aXb : a.natDegree + 1 = (X * b).natDegree := by simp_all
  have hstrictInterl_or : StrictInterl a (X * b) ∨ StrictInterl (X * b) a :=
    strictInterl_of_allComboRealRooted hap.1.1 hap.1.2 hXb_rr.1 hXb_rr.2 hall_aXb
      (Or.inl hdeg_aXb)
  have hstrictInterl_aXb : StrictInterl a (X * b) :=
    StrictInterl.forward_of_orientation_of_succDegree hdeg_aXb.symm hstrictInterl_or
  exact strictInterl_of_strictInterl_X_mul_of_nonneg hstrictInterl_aXb hb_nonneg ha_nonneg

private theorem natDegree_X_mul_component_eq_or_succ_of_strictInterl_left_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hp_eq : p = a + X * b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_top : a.natDegree = d)
    (hb0 : b ≠ 0)
    (hap : StrictInterl a p) :
    (X * b).natDegree = d ∨ (X * b).natDegree + 1 = d := by
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_addend_of_strictInterl_left hp_eq hap
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

private lemma not_isRoot_zero_of_idTransform_fixed_top_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]}
    (hfix : idTransform d p = p)
    (hdeg : p.natDegree = d)
    (hp_nonneg : HasNonnegCoeffs p)
    (hp0 : p ≠ 0) :
    ¬ p.IsRoot 0 := by
  intro hp_root0
  have hcoeff : p.coeff 0 = p.coeff d := by
    simpa [idTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using
      (congrArg (fun q => q.coeff 0) hfix).symm
  have htop : 0 < p.coeff d := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact hp_nonneg.pos_leadingCoeff hp0
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero] at hp_root0
  simp_all

private lemma exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
    {p : ℝ[X]}
    (hp_rr_ne : p ≠ 0) (hp_nonneg : HasNonnegCoeffs p)
    (hp0_root : ¬ p.IsRoot 0) :
    ∃ c : ℝ, (∀ s ∈ p.roots, s ≤ c) ∧ c < 0 := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  by_cases hrs_nil : rs = []
  · refine ⟨-1, ?_, by simp⟩
    intro s hs
    simp [← hrs_eq, hrs_nil] at hs
  · refine ⟨rs.getLast hrs_nil, ?_, ?_⟩
    · intro s hs
      apply List.Pairwise.rel_getLast hrs_sorted
      exact Multiset.mem_coe.mp (by simpa [hrs_eq] using hs)
    · have hc_root : p.IsRoot (rs.getLast hrs_nil) := by
        apply (mem_roots hp_rr_ne).mp
        simp [← hrs_eq]
      have hc_nonpos : rs.getLast hrs_nil ≤ 0 :=
        roots_nonpos_of_hasNonnegCoeffs hp_nonneg (rs.getLast hrs_nil) <|
          (mem_roots hp_rr_ne).mpr hc_root
      grind

private theorem strictInterl_b_component_of_strictInterl_left_top_of_sameDegree
    {d : ℕ} {p a b : ℝ[X]}
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hXb_top : (X * b).natDegree = d)
    (hap : StrictInterl a p) :
    StrictInterl b a := by
  have hp_eq : p = a + X * b := hid.1
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_addend_of_strictInterl_left hp_eq hap
  have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
    ⟨mul_ne_zero X_ne_zero hb0, hall_aXb.right_splits⟩
  have hsame : a.natDegree = (X * b).natDegree := by lia
  have hstrictInterl_or : StrictInterl a (X * b) ∨ StrictInterl (X * b) a :=
    strictInterl_of_allComboRealRooted hap.1.1 hap.1.2 hXb_rr.1 hXb_rr.2 hall_aXb
      (Or.inr hsame)
  have ha_not_root0 : ¬ a.IsRoot 0 :=
    not_isRoot_zero_of_idTransform_fixed_top_of_hasNonnegCoeffs
      hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      hap.1.1 ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by simp
  have hstrictInterl_aXb : StrictInterl a (X * b) :=
    PosComboRealRooted.strictInterl_of_strictInterl_or_reverse_of_root_asymmetry
      (f := X * b) (g := a) (c := c) (r := 0)
      (by lia)
      hac_le hXb_root0 hc_lt0
  exact strictInterl_of_strictInterl_X_mul_of_nonneg hstrictInterl_aXb hb_nonneg ha_nonneg

private theorem strictInterl_b_component_of_strictInterl_left_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hap : StrictInterl a p) :
    StrictInterl b a := by
  have hp_eq : p = a + X * b := hid.1
  have hXb_case :
      (X * b).natDegree = d ∨ (X * b).natDegree + 1 = d :=
    natDegree_X_mul_component_eq_or_succ_of_strictInterl_left_top
      hd hp_eq ha_nonneg hb_nonneg ha_top hb0 hap
  rcases hXb_case with hXb_top | hXb_gap
  · exact
      strictInterl_b_component_of_strictInterl_left_top_of_sameDegree
        hid ha_nonneg hb_nonneg ha0 hb0 ha_top hXb_top hap
  · exfalso
    have hall_aXb : AllComboRealRooted a (X * b) :=
      allComboRealRooted_addend_of_strictInterl_left hp_eq hap
    have hXb_rr : ((X * b) ≠ 0 ∧ (X * b).Splits) :=
      ⟨mul_ne_zero X_ne_zero hb0, hall_aXb.right_splits⟩
    have hall_Xba : AllComboRealRooted (X * b) a := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_aXb β α
    have hstrictInterl_or : StrictInterl (X * b) a ∨ StrictInterl a (X * b) := by
      have hdeg : (X * b).natDegree + 1 = a.natDegree := by lia
      exact
        strictInterl_of_allComboRealRooted
          hXb_rr.1 hXb_rr.2 hap.1.1 hap.1.2 hall_Xba (Or.inl hdeg)
    have ha_not_root0 : ¬ a.IsRoot 0 :=
      not_isRoot_zero_of_idTransform_fixed_top_of_hasNonnegCoeffs
        hid.2.2.2.1 ha_top ha_nonneg ha0
    obtain ⟨c, hac_le, hc_lt0⟩ :=
      exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
        hap.1.1 ha_nonneg ha_not_root0
    have hXb_root0 : (X * b).IsRoot 0 := by simp
    have hbad : StrictInterl a (X * b) :=
      PosComboRealRooted.strictInterl_of_strictInterl_or_reverse_of_root_asymmetry
        (f := X * b) (g := a) (c := c) (r := 0)
        hstrictInterl_or hac_le hXb_root0 hc_lt0
    have hbound : a.natDegree ≤ (X * b).natDegree := hbad.natDegree_le
    lia

private theorem strictInterl_b_component_of_strictInterl_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hbp : StrictInterl b p) :
    StrictInterl b a := by
  have hp_eq : p = a + X * b := hid.1
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hp_eq] using ha_nonneg.add hb_nonneg.X_mul
  have hpxb : StrictInterl p (X * b) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hbp hb_nonneg hp_nonneg
  have hall_aXb : AllComboRealRooted a (X * b) :=
    allComboRealRooted_left_X_mul_component_of_strictInterl_right hp_eq hpxb
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
    natDegree_right_of_strictInterl_to_sum hp_eq ha_nonneg hb_nonneg hb0 hbp
  have hsame : a.natDegree = (X * b).natDegree := by simp_all
  have ha_not_root0 : ¬ a.IsRoot 0 :=
    not_isRoot_zero_of_idTransform_fixed_top_of_hasNonnegCoeffs
      hid.2.2.2.1 ha_top ha_nonneg ha0
  obtain ⟨c, hac_le, hc_lt0⟩ :=
    exists_root_upper_bound_lt_zero_of_hasNonnegCoeffs_of_not_isRoot_zero
      ha_rr.1 ha_nonneg ha_not_root0
  have hXb_root0 : (X * b).IsRoot 0 := by simp
  have hstrictInterl_or : StrictInterl a (X * b) ∨ StrictInterl (X * b) a :=
    strictInterl_of_allComboRealRooted ha_rr.1 ha_rr.2 hpxb.2.1.1 hpxb.2.1.2 hall_aXb
      (Or.inr hsame)
  have hstrictInterl_aXb : StrictInterl a (X * b) :=
    PosComboRealRooted.strictInterl_of_strictInterl_or_reverse_of_root_asymmetry
      (f := X * b) (g := a) (c := c) (r := 0)
      (by lia)
      hac_le hXb_root0 hc_lt0
  exact strictInterl_of_strictInterl_X_mul_of_nonneg hstrictInterl_aXb hb_nonneg ha_nonneg

theorem BrandenSolus.first_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (StrictInterl b a ↔ StrictInterl a p) := ⟨fun hba ↦
  (BrandenSolus.forward_of_strictInterl_b_a
    hd hid ha_nonneg hb_nonneg hba).1,
    strictInterl_b_component_of_strictInterl_left_top
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top⟩

theorem BrandenSolus.forward_of_strictInterl_a_p_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    StrictInterl a p → StrictInterl b p ∧ StrictInterl (idTransform d p) p := fun hap ↦
  (BrandenSolus.forward_of_strictInterl_b_a hd hid ha_nonneg hb_nonneg
    ((BrandenSolus.first_equiv_of_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top).2 hap)).2

theorem BrandenSolus.second_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (StrictInterl a p ↔ StrictInterl b p) := ⟨fun hap ↦
  (BrandenSolus.forward_of_strictInterl_a_p_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hap).1,
    fun hbp ↦ (BrandenSolus.forward_of_strictInterl_b_a hd hid ha_nonneg hb_nonneg
      (strictInterl_b_component_of_strictInterl_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hbp)).1⟩

theorem BrandenSolus.third_forward_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    StrictInterl b p → StrictInterl (idTransform d p) p := fun hbp ↦
  (BrandenSolus.forward_of_strictInterl_b_a hd hid ha_nonneg hb_nonneg
    (strictInterl_b_component_of_strictInterl_right_top
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hbp)).2.2

private theorem strictInterl_b_component_of_strictInterl_Id_top_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1)
    (hIdp : StrictInterl (idTransform d p) p) :
    StrictInterl b p := by
  let h : ℝ[X] := idTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hp_nonneg : HasNonnegCoeffs p := by simpa [hp_eq] using ha_nonneg.add hb_nonneg.X_mul
  have hh_nonneg : HasNonnegCoeffs h := by simpa [hId_eq] using ha_nonneg.add hb_nonneg
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
        Polynomial.natDegree_add_eq_left_of_natDegree_lt hdeg_lt
      _ = d := ha_top
  have hdeg_lt : b.natDegree < a.natDegree := by lia
  have hh_pos : HasPosLeadingCoeff h := by
    rw [hId_eq]
    exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt ha_pos
  have hp_split : p = h + t := by grind
  have hall_ht : AllComboRealRooted h t :=
    allComboRealRooted_addend_of_strictInterl_left hp_split hIdp
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
    roots_nonpos_of_hasNonnegCoeffs hh_nonneg
  have hsame : h.natDegree = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    lia
  have hstrictInterl_or : StrictInterl h t ∨ StrictInterl t h :=
    strictInterl_of_allComboRealRooted hIdp.1.1 hIdp.1.2 ht_rr.1 ht_rr.2 hall_ht
      (Or.inr hsame)
  have ht_root1 : t.IsRoot 1 := by simp [t]
  have hht : StrictInterl h t :=
    PosComboRealRooted.strictInterl_of_strictInterl_or_reverse_of_root_asymmetry
      (f := t) (g := h) (c := 0) (r := 1)
      (by lia)
      hh_nonpos ht_root1 (by simp)
  have ht_le_one : ∀ r ∈ t.roots, r ≤ 1 := by
    intro r hr
    dsimp [t] at hr
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0), roots_X_sub_C] at hr
    rcases Multiset.mem_add.mp hr with hr | hr
    · simp_all
    · have hr0 : r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hb_nonneg r hr
      linarith
  have hbh : StrictInterl b h :=
    (interlaces_of_strictInterl_sameDegree_rightmost_factor
      (f := h) (g := t) (q := b) (uR := 1)
      hht hsame ht_le_one (by lia)).toStrictInterl
  have hb_le_one : ∀ r ∈ b.roots, r ≤ (1 : ℝ) := fun r hr ↦
    (roots_nonpos_of_hasNonnegCoeffs hb_nonneg r hr).trans (by norm_num)
  have hbt : StrictInterl b t := by
    dsimp [t]
    exact (StrictInterl.refl hb_rr.1 hb_rr.2).mul_X_sub_C_of_sameDegree_of_roots_le
      (1 : ℝ) rfl hb_pos hb_pos hb_le_one hb_le_one
  have hbp_sum : StrictInterl b [h, t].sum := by
    refine StrictInterl.sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_ <;> simp_all
  simp_all

theorem BrandenSolus.third_converse_of_top_degree_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1) :
    StrictInterl (idTransform d p) p → StrictInterl b p := by
  exact strictInterl_b_component_of_strictInterl_Id_top_of_right_top
    hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top

theorem BrandenSolus.third_equiv_of_top_degree_of_right_top
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d)
    (hb_top : b.natDegree = d - 1) :
    (StrictInterl b p ↔ StrictInterl (idTransform d p) p) := by
  constructor
  · exact BrandenSolus.third_forward_of_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  · exact BrandenSolus.third_converse_of_top_degree_of_right_top
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top

theorem BrandenSolus.third_converse_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    StrictInterl (idTransform d p) p → StrictInterl b p := by
  intro hIdp
  let h : ℝ[X] := idTransform d p
  let t : ℝ[X] := (X - C (1 : ℝ)) * b
  have hp_eq : p = a + X * b := hid.1
  have hId_eq : h = a + b := by simpa [h] using idTransform_eq_add_of_isIdDecomposition hd hid
  have hh_nonneg : HasNonnegCoeffs h := by simpa [hId_eq] using ha_nonneg.add hb_nonneg
  have ha_pos : HasPosLeadingCoeff a := ha_nonneg.pos_leadingCoeff ha0
  have hdeg_lo : b.natDegree + 1 ≤ p.natDegree := by
    simpa [hp_eq] using
      natDegree_add_X_mul_ge_of_hasNonnegCoeffs ha_nonneg hb_nonneg hb0
  have hdeg_lt : b.natDegree < a.natDegree := by lia
  have hh_deg : h.natDegree = d := by
    rw [hId_eq]
    calc
      (a + b).natDegree = a.natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt hdeg_lt
      _ = d := ha_top
  have hh_nonpos : ∀ r ∈ h.roots, r ≤ 0 :=
    roots_nonpos_of_hasNonnegCoeffs hh_nonneg
  have hp_split : p = h + t := by grind
  have hall_ht : AllComboRealRooted h t :=
    allComboRealRooted_addend_of_strictInterl_left hp_split hIdp
  have ht_ne : t ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero (1 : ℝ)) hb0
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, hall_ht.right_splits⟩
  have ht_root1 : t.IsRoot 1 := by simp [t]
  rcases natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted hall_ht hIdp.1.1 ht_ne with
    hsame | htoo_big | hgap
  · have hb_top : b.natDegree = d - 1 := by
      dsimp [t] at hsame
      rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at hsame
      lia
    exact
      BrandenSolus.third_converse_of_top_degree_of_right_top
        hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top hb_top hIdp
  · dsimp [t] at htoo_big
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C] at htoo_big
    lia
  · have hall_th : AllComboRealRooted t h := by
      intro α β
      simpa [add_comm, add_left_comm, add_assoc] using hall_ht β α
    have hstrictInterl_or : StrictInterl t h ∨ StrictInterl h t :=
      strictInterl_of_allComboRealRooted ht_rr.1 ht_rr.2 hIdp.1.1 hIdp.1.2 hall_th
        (Or.inl hgap)
    have hnot_th : ¬ StrictInterl t h := by
      intro hth
      have h1_le : (1 : ℝ) ≤ 0 :=
        hth.roots_le_of_right hh_nonpos 1 ((mem_roots hth.1.1).mpr ht_root1)
      linarith
    rcases hstrictInterl_or with hth | hht
    · lia
    · have hbound : h.natDegree ≤ t.natDegree := hht.natDegree_le
      lia

theorem BrandenSolus.third_equiv_of_top_degree
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_top : a.natDegree = d) :
    (StrictInterl b p ↔ StrictInterl (idTransform d p) p) :=
  ⟨BrandenSolus.third_forward_of_top_degree
    hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top,
    BrandenSolus.third_converse_of_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top⟩

theorem BrandenSolus.first_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (hb0 : b ≠ 0) :
    (StrictInterl b a ↔ StrictInterl a p) := ⟨fun hba ↦
  (BrandenSolus.forward_of_strictInterl_b_a
    hd hid ha_nonneg hb_nonneg hba).1,
    strictInterl_b_component_of_strictInterl_left_of_natDegree_le
      hid.1 ha_nonneg hb_nonneg ha_le hb0⟩

theorem BrandenSolus.second_equiv_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    (StrictInterl a p ↔ StrictInterl b p) := ⟨fun hap ↦
  (BrandenSolus.forward_of_strictInterl_b_a hd hid ha_nonneg hb_nonneg
      ((BrandenSolus.first_equiv_of_natDegree_le
        hd hid ha_nonneg hb_nonneg ha_le hb0).2 hap)).2.1,
    fun hbp ↦ (BrandenSolus.forward_of_strictInterl_b_a hd hid ha_nonneg hb_nonneg
      ((BrandenSolus.third_equiv_of_natDegree_le
        hd hid ha_nonneg hb_nonneg ha_le ha0 hb0).2 hbp)).1⟩

theorem hasNonnegCoeffs_pair_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs p ∧ HasNonnegCoeffs (idTransform d p) :=
  ⟨by simpa [hid.1] using ha_nonneg.add hb_nonneg.X_mul,
    by simpa [idTransform_eq_add_of_isIdDecomposition hd hid] using ha_nonneg.add hb_nonneg⟩

theorem hasNonnegCoeffs_fPolynomial_pair_of_isIdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs (fPolynomial d p) ∧
      HasNonnegCoeffs (rdTransform d (fPolynomial d p)) := by
  obtain ⟨hp_nonneg, hId_nonneg⟩ :=
    hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg
  exact ⟨hasNonnegCoeffs_fPolynomial hp_nonneg,
    by simpa [rdTransform_fPolynomial] using hasNonnegCoeffs_fPolynomial hId_nonneg⟩

theorem hasNonnegCoeffs_pair_of_isRdDecomposition {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hrd : IsRdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs p ∧ HasNonnegCoeffs (rdTransform d p) :=
  ⟨by simpa [hrd.1] using ha_nonneg.add hb_nonneg.X_mul,
    by simpa [rdTransform_eq_add_X_add_one_mul_of_isRdDecomposition hd hrd] using
      ha_nonneg.add (hasNonnegCoeffs_X_add_one.mul hb_nonneg)⟩

theorem hasNonnegCoeffs_transformed_components_of_isIdDecomposition {d : ℕ} {a b : ℝ[X]}
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    HasNonnegCoeffs (fPolynomial d a) ∧ HasNonnegCoeffs (fPolynomial (d - 1) b) :=
  ⟨hasNonnegCoeffs_fPolynomial ha_nonneg, hasNonnegCoeffs_fPolynomial hb_nonneg⟩

lemma strictInterl_iff_strictInterl_mul_X_add_one_both {f g : ℝ[X]} :
    StrictInterl ((X + 1) * f) ((X + 1) * g) ↔ StrictInterl f g := by
  constructor
  · intro h
    have h' : StrictInterl ((X - C (-1)) * f) ((X - C (-1)) * g) := by simp_all
    exact h'.of_mul_X_sub_C_both
  · intro h
    have h' : StrictInterl ((X - C (-1)) * f) ((X - C (-1)) * g) :=
      h.mul_X_sub_C_both (-1)
    simp_all

lemma strictInterl_iff_strictInterl_mul_X_add_one_pow_both {n : ℕ} {f g : ℝ[X]} :
    StrictInterl ((X + 1) ^ n * f) ((X + 1) ^ n * g) ↔ StrictInterl f g := by
  induction n with
  | zero => lia
  | succ n ih =>
      have hstep :
          StrictInterl ((X + 1) * ((X + 1) ^ n * f)) ((X + 1) * ((X + 1) ^ n * g)) ↔
            StrictInterl ((X + 1) ^ n * f) ((X + 1) ^ n * g) :=
        strictInterl_iff_strictInterl_mul_X_add_one_both
      grind

/-- The `f`-polynomial transform preserves the oriented interlacing relation on
nonnegative-coefficient pairs in the minimal ambient degree
`max u.natDegree v.natDegree`. -/
theorem strictInterlFPolynomialTransportMinimal {d : ℕ} {u v : ℝ[X]}
    (hd : d = max u.natDegree v.natDegree)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    StrictInterl (fPolynomial d u) (fPolynomial d v) ↔ StrictInterl u v := by
  constructor
  · intro h
    have hud : u.natDegree ≤ d := by simp_all
    have hvd : v.natDegree ≤ d := by simp_all
    have hu_rr : (u ≠ 0 ∧ u.Splits) :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hud h.1.1 h.1.2 hu_nonneg
    have hv_rr : (v ≠ 0 ∧ v.Splits) :=
      isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs hvd h.2.1.1 h.2.1.2 hv_nonneg
    exact strictInterl_of_strictInterl_fPolynomial_of_minimal_of_isRealRooted_of_hasNonnegCoeffs
      hd hu_rr.1 hu_rr.2 hv_rr.1 hv_rr.2 h hu_nonneg hv_nonneg
  · intro h
    exact
      strictInterl_fPolynomial_of_strictInterl_of_hasNonnegCoeffs_of_minimal
        hd h hu_nonneg hv_nonneg

/-- The `f`-polynomial transform preserves the oriented interlacing relation on
nonnegative-coefficient pairs of degree at most `d`.  Larger ambient degrees
only add a common power of `X + 1` to both transformed polynomials. -/
theorem strictInterlFPolynomialTransport {d : ℕ} {u v : ℝ[X]}
    (hud : u.natDegree ≤ d) (hvd : v.natDegree ≤ d)
    (hu_nonneg : HasNonnegCoeffs u) (hv_nonneg : HasNonnegCoeffs v) :
    StrictInterl (fPolynomial d u) (fPolynomial d v) ↔ StrictInterl u v := by
  let m := max u.natDegree v.natDegree
  have hum : u.natDegree ≤ m := le_max_left _ _
  have hvm : v.natDegree ≤ m := le_max_right _ _
  have hmd : m ≤ d := max_le hud hvd
  have hu_pad : fPolynomial d u = (X + 1) ^ (d - m) * fPolynomial m u := by
    simpa [m] using fPolynomial_pad_by_X_add_one_pow hum hmd
  have hv_pad : fPolynomial d v = (X + 1) ^ (d - m) * fPolynomial m v := by
    simpa [m] using fPolynomial_pad_by_X_add_one_pow hvm hmd
  calc
    StrictInterl (fPolynomial d u) (fPolynomial d v)
        ↔ StrictInterl ((X + 1) ^ (d - m) * fPolynomial m u)
          ((X + 1) ^ (d - m) * fPolynomial m v) := by lia
    _ ↔ StrictInterl (fPolynomial m u) (fPolynomial m v) :=
          strictInterl_iff_strictInterl_mul_X_add_one_pow_both
    _ ↔ StrictInterl u v :=
      strictInterlFPolynomialTransportMinimal (d := m) rfl hu_nonneg hv_nonneg

theorem BrandenSolus.last_equiv
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b) :
    (StrictInterl (idTransform d p) p ↔
      StrictInterl (rdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  rcases hasNonnegCoeffs_pair_of_isIdDecomposition hd hid ha_nonneg hb_nonneg with
    ⟨hp_nonneg, hId_nonneg⟩
  rw [rdTransform_fPolynomial]
  exact (strictInterlFPolynomialTransport
    (u := idTransform d p) (v := p)
    (idTransform_natDegree_le hd) hd hId_nonneg hp_nonneg).symm

private lemma strictInterl_iff_of_eq_X_mul
    {f g f' g' : ℝ[X]} (hf : f = X * f') (hg : g = X * g')
    (hfnn : HasNonnegCoeffs f') (hgnn : HasNonnegCoeffs g') :
    StrictInterl f g ↔ StrictInterl f' g' := by
  simpa only [hf, hg] using
    (strictInterl_iff_strictInterl_mul_X_both_of_hasNonnegCoeffs hfnn hgnn).symm

private theorem BrandenSolus.descend_of_lt_top
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
        (StrictInterl b' a' ↔ StrictInterl a' q) ∧
        (StrictInterl a' q ↔ StrictInterl b' q) ∧
        (StrictInterl b' q ↔ StrictInterl (idTransform (d - 2) q) q) ∧
        (StrictInterl (idTransform (d - 2) q) q ↔
          StrictInterl (rdTransform (d - 2) (fPolynomial (d - 2) q)) (fPolynomial (d - 2) q))) :
    (StrictInterl b a ↔ StrictInterl a p) ∧
    (StrictInterl a p ↔ StrictInterl b p) ∧
    (StrictInterl b p ↔ StrictInterl (idTransform d p) p) ∧
    (StrictInterl (idTransform d p) p ↔
      StrictInterl (rdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
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
  have hIdq_nonneg : HasNonnegCoeffs (idTransform (d - 2) q) := hpair_nonneg.2
  have hpX' : p = X * q := by lia
  have hIdX : idTransform d p = X * idTransform (d - 2) q := by
    calc
      idTransform d p = idTransform d (X * q) := by lia
      _ = X * idTransform (d - 2) q :=
        idTransform_X_mul_of_natDegree_le_two_pred hd2 hqdeg
  have hsmall := hprev hqdeg hidq ha'_nonneg hb'_nonneg ha'0 hb'0
  rcases hsmall with ⟨hfirst_small, hsecond_small, hthird_small, -⟩
  have hba_transport := strictInterl_iff_of_eq_X_mul hbX haX hb'_nonneg ha'_nonneg
  have hap_transport := strictInterl_iff_of_eq_X_mul haX hpX' ha'_nonneg hq_nonneg
  have hbp_transport := strictInterl_iff_of_eq_X_mul hbX hpX' hb'_nonneg hq_nonneg
  have hIdp_transport :
      StrictInterl (idTransform d p) p ↔ StrictInterl (idTransform (d - 2) q) q :=
    strictInterl_iff_of_eq_X_mul hIdX hpX' hIdq_nonneg hq_nonneg
  refine ⟨?_, ?_, ?_, BrandenSolus.last_equiv hd hid ha_nonneg hb_nonneg⟩ <;> lia

/-- The naive fully strict translation of Brändén--Solus Theorem 2.6, without
the hypotheses `a ≠ 0` and `b ≠ 0`, is false: our `StrictInterl` predicate is
reflexive on real-rooted polynomials and excludes the zero polynomial, so the
degree-zero decomposition `1 = 1 + X * 0` breaks the first equivalence. -/
theorem BrandenSolus.not_naive :
    ¬ ∀ {d : ℕ} {p a b : ℝ[X]},
    p.natDegree ≤ d →
    IsIdDecomposition d p a b →
    HasNonnegCoeffs a →
    HasNonnegCoeffs b →
    (StrictInterl b a ↔ StrictInterl a p) ∧
    (StrictInterl a p ↔ StrictInterl b p) ∧
    (StrictInterl b p ↔ StrictInterl (idTransform d p) p) ∧
    (StrictInterl (idTransform d p) p ↔
      StrictInterl (rdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  intro h
  have hcase := (h (d := 0) (p := (1 : ℝ[X])) (a := (1 : ℝ[X])) (b := 0)
    (by simp)
    (by refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [idTransform])
    hasNonnegCoeffs_one hasNonnegCoeffs_zero).1
  exact (hcase.mpr (StrictInterl.refl (by simp) (by simp))).1.1 rfl

/-- In the ordered-degree branch `a.natDegree ≤ b.natDegree`, the forward half
of the remaining bridge is already available: once `b` interlaces `p`, the
existing component theorem recovers `b ≺ a`, and the forward Brändén--Solus
implication then yields `idTransform d p ≺ p`. -/
theorem BrandenSolus.ordered_bridge_forward_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha_le : a.natDegree ≤ b.natDegree)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    StrictInterl b p → StrictInterl (idTransform d p) p := fun hbp ↦
  (BrandenSolus.forward_of_strictInterl_b_a hd hid ha_nonneg hb_nonneg
    ((BrandenSolus.third_equiv_of_natDegree_le
      hd hid ha_nonneg hb_nonneg ha_le ha0 hb0).2 hbp)).2.2

/-- Ordered-degree converse bridge: if `a.natDegree ≤ b.natDegree` and
`idTransform d p ≺ p`, then already `b ≺ p`.

The proof rewrites `p` as `idTransform d p + (X - 1) * b`, extracts
`b ≺ idTransform d p` from the shifted pair via the same-degree Obreschkoff
converse, and then sums back to `b ≺ p`. -/
theorem BrandenSolus.ordered_bridge_converse_of_natDegree_le
    {d : ℕ} {p a b : ℝ[X]}
    (hd : p.natDegree ≤ d)
    (hid : IsIdDecomposition d p a b)
    (ha_nonneg : HasNonnegCoeffs a)
    (hb_nonneg : HasNonnegCoeffs b)
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (ha_le : a.natDegree ≤ b.natDegree) :
    StrictInterl (idTransform d p) p → StrictInterl b p := by
  intro hIdp
  let h : ℝ[X] := idTransform d p
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
      exact Polynomial.natDegree_add_eq_right_of_natDegree_lt hdeg_lt
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
  have hall_ht : AllComboRealRooted h t :=
    allComboRealRooted_addend_of_strictInterl_left hp_split hIdp
  have ht_rr : (t ≠ 0 ∧ t.Splits) :=
    ⟨ht_ne, hall_ht.right_splits⟩
  have hb_rr : (b ≠ 0 ∧ b.Splits) := by
    apply isRealRooted_of_dvd ht_rr.1 ht_rr.2 hb0
    refine ⟨X - C (1 : ℝ), ?_⟩
    grind
  have hb_le : ∀ s ∈ b.roots, s ≤ (1 : ℝ) := fun s hs ↦
    (roots_nonpos_of_hasNonnegCoeffs hb_nonneg s hs).trans (by norm_num)
  have hh_le : ∀ s ∈ h.roots, s ≤ (1 : ℝ) := fun s hs ↦
    (roots_nonpos_of_hasNonnegCoeffs hh_nonneg s hs).trans (by norm_num)
  have ht_deg : h.natDegree + 1 = t.natDegree := by
    dsimp [t]
    rw [hh_deg, natDegree_mul (X_sub_C_ne_zero (1 : ℝ)) hb0, natDegree_X_sub_C]
    lia
  have hht_or : StrictInterl h t ∨ StrictInterl t h :=
    strictInterl_of_allComboRealRooted hh_rr.1 hh_rr.2 ht_rr.1 ht_rr.2 hall_ht
      (Or.inl ht_deg)
  have hht : StrictInterl h t :=
    StrictInterl.forward_of_orientation_of_succDegree ht_deg.symm hht_or
  have hbh : StrictInterl b h :=
    hht.of_mul_X_sub_C_of_sameDegree_of_roots_le
      hh_deg.symm hb_pos hh_pos hb_le hh_le
  have hbt : StrictInterl b t :=
    (StrictInterl.refl hb_rr.1 hb_rr.2).mul_X_sub_C_of_sameDegree_of_roots_le
      (1 : ℝ) rfl hb_pos hb_pos hb_le hb_le
  have hbp_sum : StrictInterl b [h, t].sum := by
    refine StrictInterl.sum_left_of_common_left [h, t] b ?_ hb_pos ?_ ?_ <;> simp_all
  simp_all

/-- Top-degree boundary case of Brändén--Solus Theorem 2.6: the left
`I_d`-component occupies the full ambient degree. -/
theorem BrandenSolus.topDegreeBoundary :
    ∀ {d : ℕ} {p a b : ℝ[X]},
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      a.natDegree = d →
      (StrictInterl b a ↔ StrictInterl a p) ∧
      (StrictInterl a p ↔ StrictInterl b p) ∧
      (StrictInterl b p ↔ StrictInterl (idTransform d p) p) ∧
      (StrictInterl (idTransform d p) p ↔
        StrictInterl (rdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  intro d p a b hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
  exact ⟨BrandenSolus.first_equiv_of_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top,
    BrandenSolus.second_equiv_of_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top,
    BrandenSolus.third_equiv_of_top_degree
      hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top,
    BrandenSolus.last_equiv hd hid ha_nonneg hb_nonneg⟩

/-- Brändén--Solus Theorem 2.6 in the nondegenerate `StrictInterl` language.
The extra assumptions `a ≠ 0` and `b ≠ 0` remove the zero-polynomial edge cases
where the paper's strict interlacing language and `StrictInterl` diverge; see
`BrandenSolus.not_naive`.  The degree-ordered branch uses the ordered
bridge lemmas, the top-degree branch uses
`BrandenSolus.topDegreeBoundary`, and the remaining branch descends by
a common factor of `X`. -/
theorem BrandenSolus.strictInterl_iff_of_isIdDecomposition :
    ∀ {d : ℕ} {p a b : ℝ[X]},
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      (StrictInterl b a ↔ StrictInterl a p) ∧
      (StrictInterl a p ↔ StrictInterl b p) ∧
      (StrictInterl b p ↔ StrictInterl (idTransform d p) p) ∧
      (StrictInterl (idTransform d p) p ↔
        StrictInterl (rdTransform d (fPolynomial d p)) (fPolynomial d p)) := by
  let P : ℕ → Prop := fun d =>
    ∀ (p a b : ℝ[X]),
      p.natDegree ≤ d →
      IsIdDecomposition d p a b →
      HasNonnegCoeffs a →
      HasNonnegCoeffs b →
      a ≠ 0 →
      b ≠ 0 →
      (StrictInterl b a ↔ StrictInterl a p) ∧
      (StrictInterl a p ↔ StrictInterl b p) ∧
      (StrictInterl b p ↔ StrictInterl (idTransform d p) p) ∧
      (StrictInterl (idTransform d p) p ↔
        StrictInterl (rdTransform d (fPolynomial d p)) (fPolynomial d p))
  have hmain : ∀ d, P d := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih p a b hd hid ha_nonneg hb_nonneg ha0 hb0
    have ha_deg : a.natDegree ≤ d := hid.2.1
    have hb_deg : b.natDegree ≤ d - 1 := hid.2.2.1
    by_cases ha_le : a.natDegree ≤ b.natDegree
    · refine ⟨?_, ?_, ?_, BrandenSolus.last_equiv hd hid ha_nonneg hb_nonneg⟩
      · exact BrandenSolus.first_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le hb0
      · exact BrandenSolus.second_equiv_of_natDegree_le
          hd hid ha_nonneg hb_nonneg ha_le ha0 hb0
      · exact ⟨BrandenSolus.ordered_bridge_forward_of_natDegree_le
            hd hid ha_nonneg hb_nonneg ha_le ha0 hb0,
          BrandenSolus.ordered_bridge_converse_of_natDegree_le
            hd hid ha_nonneg hb_nonneg ha0 hb0 ha_le⟩
    · by_cases ha_top : a.natDegree = d
      · exact BrandenSolus.topDegreeBoundary hd hid ha_nonneg hb_nonneg ha0 hb0 ha_top
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
              (StrictInterl b' a' ↔ StrictInterl a' q) ∧
              (StrictInterl a' q ↔ StrictInterl b' q) ∧
              (StrictInterl b' q ↔ StrictInterl (idTransform (d - 2) q) q) ∧
              (StrictInterl (idTransform (d - 2) q) q ↔
                StrictInterl (rdTransform (d - 2) (fPolynomial (d - 2) q))
                  (fPolynomial (d - 2) q)) := by
          grind
        exact BrandenSolus.descend_of_lt_top
          hd hd2 hid ha_nonneg hb_nonneg ha0 hb0 ha_lt hb_lt hprev
  simpa [P] using hmain

end RealRooted
