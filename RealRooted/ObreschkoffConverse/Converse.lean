import RealRooted.ObreschkoffConverse.Regularization

/-!
# Obreschkoff converse endgame

Root-sign assembly and common-root descent from all-real-rooted pencils to
proper position.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- Same-degree companion to
`interlaces_of_consecutive_signs_of_natDegree_lt`: if a nonzero polynomial `F`
has strict sign changes on consecutive roots of a real-rooted polynomial `f`,
has the same degree as `f`, and has one extra outer root on either side, then
`F` is real-rooted. This is the exact assembly step needed for the non-cancel
opposite-sign branch in the forward same-degree Obreschkoff theorem. -/
private theorem isRealRooted_of_consecutive_signs_of_natDegree_eq_of_outer_root
    {f F : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0)
    (hdeg : F.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ f.natDegree)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (houter :
      (∃ uL, F.IsRoot uL ∧ ∀ r, f.IsRoot r → uL < r) ∨
      (∃ uR, F.IsRoot uR ∧ ∀ r, f.IsRoot r → r < uR)) : (F ≠ 0 ∧ F.Splits) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := F) hrs_sorted (by grind)
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
      card_roots_of_splits hf_splits]
  have hrs_ne : rs ≠ [] := by grind
  have hus_sub : (↑us : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    simp_all
  have hus_len_deg : us.length = F.natDegree - 1 := by lia
  rcases houter with ⟨uL, huL_root, huL_lt⟩ | ⟨uR, huR_root, huR_lt⟩
  · obtain ⟨r₀, rs', hrs_cons⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
      cases h : rs with
      | nil => lia
      | cons r₀ rs' =>
          lia
    have hr₀_root : f.IsRoot r₀ := by
      apply (mem_roots hf_ne).mp
      rw [← hrs_eq, hrs_cons]
      simp
    have hus_int' : ListInterlaces us (r₀ :: rs') := by lia
    have huL_lt_all_us : ∀ u ∈ us, uL < u :=
      fun u hu =>
        lt_of_lt_of_le (huL_lt r₀ hr₀_root)
          (listInterlaces_all_ge us rs' r₀ hus_int' u hu)
    have hws_pw : (uL :: us).Pairwise (· < ·) := by simp_all
    have hws_sub : (↑(uL :: us) : Multiset ℝ) ≤ F.roots := by
      rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
      intro x hx
      rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx' <;> simp_all
    have hws_len : (uL :: us).length = F.natDegree := by simp_all
    have hws_eq : (↑(uL :: us) : Multiset ℝ) = F.roots :=
      Multiset.eq_of_le_of_card_le hws_sub (by
        calc
          F.roots.card ≤ F.natDegree := card_roots' F
          _ = (uL :: us).length := hws_len.symm
          _ = (↑(uL :: us) : Multiset ℝ).card := (Multiset.coe_card _).symm)
    refine ⟨hF_ne, ?_⟩
    exact splits_of_card_roots (by rw [← hws_eq, Multiset.coe_card, hws_len])
  · have hu_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have hu_root : f.IsRoot (rs.getLast hrs_ne) := by
      apply (mem_roots hf_ne).mp
      rw [← hrs_eq]
      simp
    have hus_lt_all_uR : ∀ u ∈ us, u < uR :=
      fun u hu =>
        lt_of_le_of_lt
          (listInterlaces_all_le_getLast hrs_ne hrs_sorted hus_int u hu)
          (huR_lt _ hu_root)
    have hws_pw : (us ++ [uR]).Pairwise (· < ·) := by grind
    have hws_sub : (↑(us ++ [uR]) : Multiset ℝ) ≤ F.roots := by
      rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
      intro x hx
      rcases List.mem_append.mp (Multiset.mem_coe.mp hx) with hx_us | hx_uR <;> simp_all
    have hws_len : (us ++ [uR]).length = F.natDegree := by simp_all
    have hws_eq : (↑(us ++ [uR]) : Multiset ℝ) = F.roots :=
      Multiset.eq_of_le_of_card_le hws_sub (by
        calc
          F.roots.card ≤ F.natDegree := card_roots' F
          _ = (us ++ [uR]).length := hws_len.symm
          _ = (↑(us ++ [uR]) : Multiset ℝ).card := (Multiset.coe_card _).symm)
    refine ⟨hF_ne, ?_⟩
    exact splits_of_card_roots (by rw [← hws_eq, Multiset.coe_card, hws_len])

-- This private sign-change theorem is near the default heartbeat limit after
-- dependency rebuilds; the proof term is unchanged.
/-- Same-degree `hroot_sign` real-rootedness without assuming the target has
positive leading coefficient.

The positive-leading branch is already Ma--Wang:
`prec_of_interlaces_eval_mul_neg_same`. The genuinely new content here is the
negative-leading branch: strict sign changes still force real-rootedness, but
the extra root now comes from the left endpoint rather than the right. This is
exactly the helper needed for the opposite-sign, non-cancel branch in the
forward same-degree Obreschkoff theorem. -/
theorem ObreschkoffConverseInternal.isRealRooted_of_interlaces_eval_mul_neg_same_any_lc
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : F.natDegree = f.natDegree)
    (hdeg_pos : 2 ≤ f.natDegree)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) : (F ≠ 0 ∧ F.Splits) := by
  by_cases hF_pos : HasPosLeadingCoeff F
  · exact (prec_of_interlaces_eval_mul_neg_same hgf hg_pos hF_pos hdeg hroot_sign).2.1
  obtain ⟨hf, hg, hgdeg, rs0, ss, hrs0_sorted, hss_sorted, hrs0_eq, hss_eq, hint0⟩ := hgf
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs0_eq_rs : rs0 = rs := by
    apply List.Perm.eq_of_pairwise' hrs0_sorted hrs_sorted
    exact Multiset.coe_eq_coe.mp (hrs0_eq.trans hrs_eq.symm)
  subst hrs0_eq_rs
  have hint : ListInterlaces ss rs := by lia
  have hgf' : Interlaces g f :=
    ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq,
      hss_eq, hint⟩
  have hF_natdeg_pos : 0 < F.natDegree := by lia
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [h0] at hF_natdeg_pos
  have hF_lc_ne : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF_ne
  have hF_lc_neg : F.leadingCoeff < 0 :=
    lt_of_le_of_ne (not_lt.mp hF_pos) hF_lc_ne
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by lia, Multiset.length_sort, card_roots_of_splits hf.2]
  have hrs_ne : rs ≠ [] := by
    intro h
    rw [h] at hrs_len
    simp only [List.length_nil] at hrs_len
    lia
  obtain ⟨r₀, rs', hrs_cons⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
    cases h : rs with
    | nil => contradiction
    | cons r₀ rs' => exact ⟨r₀, rs', rfl⟩
  have hint_cons : ListInterlaces ss (r₀ :: rs') := by
    rw [← hrs_cons]
    exact hint
  have hhead_eq : rs.head! = r₀ := by simp [hrs_cons]
  have hr₀_root : f.IsRoot r₀ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq, hrs_cons]
    simp
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hprod := hroot_sign r hr
    rw [hgr, mul_zero] at hprod
    linarith
  have hhead_lt_roots_g : ∀ t ∈ g.roots, r₀ < t := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      rw [hss_eq]
      exact ht
    have hr₀_le_t : r₀ ≤ t := listInterlaces_all_ge ss rs' r₀ hint_cons t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    refine lt_of_le_of_ne hr₀_le_t ?_
    intro hEq
    subst hEq
    exact hno_g_at_f r₀ hr₀_root ht_root
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hEq_rs : rs = pre ++ r₁ :: r₂ :: rest := hEq
    have hr₁_mem : r₁ ∈ rs := by
      rw [hEq_rs]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr₁_mem
    have hr₂_mem : r₂ ∈ rs := by
      rw [hEq_rs]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr₂_mem
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg : g.eval r₁ * g.eval r₂ < 0 :=
      eval_mul_eval_neg_of_interlaces_consecutive_of_no_common hgf' hno_g_at_f pre hEq
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg
  have hnegF_pos : HasPosLeadingCoeff (C (-1 : ℝ) * F) := by
    simpa using (hasPosLeadingCoeff_neg hF_lc_neg : HasPosLeadingCoeff (-F))
  have hnegF_deg : (C (-1 : ℝ) * F).natDegree = f.natDegree := by
    have h_eq : C (-1 : ℝ) * F = -F := by simp only [map_neg, map_one, neg_mul, one_mul]
    rw [h_eq, natDegree_neg, hdeg]
  have hnegF_natdeg_pos : 0 < (C (-1 : ℝ) * F).natDegree := by
    rw [hnegF_deg]
    lia
  have hnegF_deg_pos : 0 < (C (-1 : ℝ) * F).degree :=
    natDegree_pos_iff_degree_pos.mp hnegF_natdeg_pos
  have hleft :
      ∃ uL, F.IsRoot uL ∧ ∀ r, f.IsRoot r → uL < r := by
    rcases Nat.even_or_odd f.natDegree with hf_even | hf_odd
    · have hg_odd : Odd g.natDegree := by
        have h_even : Even (g.natDegree + 1) := by
          rw [hgdeg]
          exact hf_even
        rcases h_even with ⟨k, hk⟩
        use k - 1
        lia
      have hg_left_neg : g.eval r₀ < 0 :=
        eval_neg_of_all_roots_gt_of_odd hg.1 hg_pos hg_odd hhead_lt_roots_g
      have hF_left_pos : 0 < F.eval r₀ := by
        have hprod := hroot_sign r₀ hr₀_root
        nlinarith
      have hnegF_left_neg : (C (-1 : ℝ) * F).eval r₀ < 0 := by
        rw [eval_mul, eval_C]
        linarith
      have hnegF_even : Even (C (-1 : ℝ) * F).natDegree := by
        rw [hnegF_deg]
        exact hf_even
      have ht :
          Filter.Tendsto (fun x => (C (-1 : ℝ) * F).eval x) Filter.atBot Filter.atTop :=
        tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hnegF_pos hnegF_deg_pos hnegF_even
      obtain ⟨uL, huL_le, huL_root_neg⟩ :=
        exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hnegF_left_neg ht
      have huL_root : F.IsRoot uL := by
        rw [Polynomial.IsRoot.def] at huL_root_neg ⊢
        rw [eval_mul, eval_C] at huL_root_neg
        linarith
      have huL_lt_r₀ : uL < r₀ := by
        refine lt_of_le_of_ne huL_le ?_
        intro hEq
        subst hEq
        exact ne_of_lt hnegF_left_neg huL_root_neg
      refine ⟨uL, huL_root, ?_⟩
      intro r hr
      have hr_mem : r ∈ rs := by
        have hr_roots : r ∈ f.roots := (mem_roots hf.1).mpr hr
        rw [← hrs_eq] at hr_roots
        exact Multiset.mem_coe.mp hr_roots
      have hr₀_le_r : r₀ ≤ r := by
        rw [← hhead_eq]
        exact hrs_sorted.head!_le hr_mem
      linarith
    · have hg_even : Even g.natDegree := by
        have h_odd : Odd (g.natDegree + 1) := by
          rw [hgdeg]
          exact hf_odd
        rcases h_odd with ⟨k, hk⟩
        use k
        lia
      have hg_left_pos : 0 < g.eval r₀ :=
        eval_pos_of_all_roots_gt_of_even hg.1 hg_pos hg_even hhead_lt_roots_g
      have hF_left_neg : F.eval r₀ < 0 := by
        have hprod := hroot_sign r₀ hr₀_root
        nlinarith
      have hnegF_left_pos : 0 < (C (-1 : ℝ) * F).eval r₀ := by
        rw [eval_mul, eval_C]
        linarith
      have hnegF_odd : Odd (C (-1 : ℝ) * F).natDegree := by
        rw [hnegF_deg]
        exact hf_odd
      have ht :
          Filter.Tendsto (fun x => (C (-1 : ℝ) * F).eval x) Filter.atBot Filter.atBot :=
        tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hnegF_pos hnegF_deg_pos hnegF_odd
      obtain ⟨uL, huL_le, huL_root_neg⟩ :=
        exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hnegF_left_pos ht
      have huL_root : F.IsRoot uL := by
        rw [Polynomial.IsRoot.def] at huL_root_neg ⊢
        rw [eval_mul, eval_C] at huL_root_neg
        linarith
      have huL_lt_r₀ : uL < r₀ := by
        refine lt_of_le_of_ne huL_le ?_
        intro hEq
        subst hEq
        exact ne_of_gt hnegF_left_pos huL_root_neg
      refine ⟨uL, huL_root, ?_⟩
      intro r hr
      have hr_mem : r ∈ rs := by
        have hr_roots : r ∈ f.roots := (mem_roots hf.1).mpr hr
        rw [← hrs_eq] at hr_roots
        exact Multiset.mem_coe.mp hr_roots
      have hr₀_le_r : r₀ ≤ r := by
        rw [← hhead_eq]
        exact hrs_sorted.head!_le hr_mem
      linarith
  exact
    isRealRooted_of_consecutive_signs_of_natDegree_eq_of_outer_root
      hf.1 hf.2 hF_ne hdeg (by lia) hsign (Or.inl hleft)

private theorem prec_of_allComboRealRooted_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        (f ≠ 0 ∧ f.Splits) → (g ≠ 0 ∧ g.Splits) →
        AllComboRealRooted f g →
        (f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f)
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          (f ≠ 0 ∧ f.Splits) → (g ≠ 0 ∧ g.Splits) →
          AllComboRealRooted f g →
          (f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) →
          Prec f g ∨ Prec g f)
      f.natDegree ?_ rfl ⟨hf_ne, hf_splits⟩ ⟨hg_ne, hg_splits⟩ hall hdeg
  intro n ih f g hfdeg hf hg hall hdeg
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · simp_all
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
    obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
    have hqf_ne : qf ≠ 0 := by simp_all
    have hqg_ne : qg ≠ 0 := by simp_all
    have hqf_rr : (qf ≠ 0 ∧ qf.Splits) :=
      isRealRooted_of_dvd hf.1 hf.2 hqf_ne ⟨X - C r, by grind⟩
    have hqg_rr : (qg ≠ 0 ∧ qg.Splits) :=
      isRealRooted_of_dvd hg.1 hg.2 hqg_ne ⟨X - C r, by grind⟩
    have hqhall : AllComboRealRooted qf qg :=
      allComboRealRooted_common_root_reduction hqf hqg hall
    have hqdeg : qf.natDegree + 1 = qg.natDegree ∨ qf.natDegree = qg.natDegree := by
      rcases hdeg with hsucc | hsame
      · rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
          hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsucc
        lia
      · rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
          hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsame
        lia
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hprec_q : Prec qf qg ∨ Prec qg qf :=
      ih qf.natDegree hqf_deg_lt rfl hqf_rr hqg_rr hqhall hqdeg
    rcases hprec_q with hprec_q | hprec_q
    · have hprec_mul : Prec ((X - C r) * qf) ((X - C r) * qg) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hprec_q
      lia
    · have hprec_mul : Prec ((X - C r) * qg) ((X - C r) * qf) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hprec_q
      lia
/-- **Obreschkoff's theorem** (Brändén, Theorem 7.7.3): `f` and `g` interlace
if and only if every polynomial in the real linear span `{αf + βg : α, β ∈ ℝ}`
is real-rooted (or zero).

Forward direction: interlacing → all combinations real-rooted.
This follows from Wagner addition (already proved). -/
theorem prec_of_allComboRealRooted {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f := by
  refine prec_of_allComboRealRooted_of_no_common ?_ hf_ne hf_splits hg_ne hg_splits hall hdeg
  intro f g hf hg hall hdeg hno
  let eps : ℝ := 1
  have heps : 0 < eps := by grind
  let n : ℕ := max f.natDegree g.natDegree
  have hsimple_data :
      AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∧
        ((iterateTDeriv eps n f) ≠ 0 ∧ (iterateTDeriv eps n f).Splits) ∧
        ((iterateTDeriv eps n g) ≠ 0 ∧ (iterateTDeriv eps n g).Splits) ∧
        HasSimpleRoots (iterateTDeriv eps n f) ∧
        HasSimpleRoots (iterateTDeriv eps n g) ∧
        ((iterateTDeriv eps n f).natDegree + 1 = (iterateTDeriv eps n g).natDegree ∨
            (iterateTDeriv eps n f).natDegree = (iterateTDeriv eps n g).natDegree) := by
    simpa [n] using
      simple_pair_of_allComboRealRooted_iterateTDeriv hf.1 hg.1 hf.2 hg.2 hall hdeg heps
  rcases hsimple_data with ⟨hall_iter, _, _, hf_simple, hg_simple, _⟩
  have hprec_iter :
      Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∨
        Prec (iterateTDeriv eps n g) (iterateTDeriv eps n f) := by
    simpa [n] using
      ObreschkoffConverseInternal.precOrRevPrecRegularized
        hf.1 hf.2 hg.1 hg.2 hall hdeg heps hno
  have hlead_f_iter :
      (iterateTDeriv eps n f).leadingCoeff = f.leadingCoeff := by
    simp
  have hlead_g_iter :
      (iterateTDeriv eps n g).leadingCoeff = g.leadingCoeff := by
    simp
  have hpos_f_iter :
      HasPosLeadingCoeff (iterateTDeriv eps n f) ↔ HasPosLeadingCoeff f := by
    simp
  have hpos_g_iter :
      HasPosLeadingCoeff (iterateTDeriv eps n g) ↔ HasPosLeadingCoeff g := by
    simp
  have hsucc_iter_forced :
      f.natDegree + 1 = g.natDegree →
        Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
    intro hsucc
    simpa [n] using
      ObreschkoffConverseInternal.prec_iterateTDeriv_of_allComboRealRooted_succ_of_no_common
        hf.1 hf.2 hg.1 hg.2 hall hsucc heps hno
  have hcombo_original :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g)) := by
    by_cases hmax0 : max f.natDegree g.natDegree = 0
    · have hfdeg0 : f.natDegree = 0 := by simp_all
      have hgdeg0 : g.natDegree = 0 := by simp_all
      have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hfdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg0
      intro α β
      by_cases hcomb : C α * f + C β * g = 0
      · lia
      · rw [hfC, hgC] at hcomb ⊢
        let c : ℝ := α * f.coeff 0 + β * g.coeff 0
        have hsum_eq :
            C α * C (f.coeff 0) + C β * C (g.coeff 0) =
              C c := by
          grind
        have hconst_ne : C c ≠ 0 := by lia
        have hcoeff_ne : c ≠ 0 := by grind
        have hnat0 :
            (C α * C (f.coeff 0) + C β * C (g.coeff 0)).natDegree = 0 := by
          rw [hsum_eq]
          simp
        right
        refine ⟨?_, ?_⟩
        · exact isRealRooted_of_deg_zero hcomb hnat0
        · rw [hsum_eq]
          intro r hr
          have : c = 0 := by simpa [Polynomial.IsRoot.def, c] using hr
          lia
    · have hmax_pos : 0 < max f.natDegree g.natDegree := Nat.pos_of_ne_zero hmax0
      have hW_ne : ∀ x : ℝ, (ObreschkoffConverseInternal.wronskianPoly f g).eval x ≠ 0 := by
        intro x hw
        obtain ⟨p, q, hp_def, hq_case, hpq_all, hpq_no, hp_root, hp_der_root, hq_eval_ne⟩ :=
          ObreschkoffConverseInternal.exists_special_pair_of_wronskian_zero hall hno hw
        have hq0 : q ≠ 0 := by lia
        have hq_rr : (q ≠ 0 ∧ q.Splits) := by lia
        have hp0 : p ≠ 0 := by
          rcases hq_case with ⟨hgx0, hqf⟩ | ⟨hgx_ne, hqg⟩
          · simp_all
          · intro hp0
            have hlin : C (g.eval x) * f + C (-f.eval x) * g = 0 := by lia
            by_cases hfx0 : f.eval x = 0
            · simp_all
            · by_cases hf_deg_pos : 0 < f.natDegree
              · exact
                  ObreschkoffConverseInternal.no_nontrivial_linear_relation_of_no_common_root
                    hf.1 hf.2 hno hf_deg_pos hgx_ne (neg_ne_zero.mpr hfx0) hlin
              · have hfdeg0 : f.natDegree = 0 := Nat.eq_zero_of_not_pos hf_deg_pos
                rcases hdeg with hsucc | hsame
                · have hEq : C (g.eval x) * f = C (f.eval x) * g := by grind
                  have hscalar : f = C (f.eval x / g.eval x) * g := by
                    ext n
                    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq
                    grind
                  have hdeg_eq : f.natDegree = g.natDegree := by
                    rw [hscalar, natDegree_C_mul (div_ne_zero hfx0 hgx_ne)]
                  lia
                · simp_all
        have hp_rr : (p ≠ 0 ∧ p.Splits) :=
          ⟨hp0, by simpa using hpq_all 1 0⟩
        have hq_not_root : ¬ q.IsRoot x := by simp_all
        have hp_mult_gt : 1 < p.rootMultiplicity x :=
          (one_lt_rootMultiplicity_iff_isRoot hp0).2 ⟨hp_root, hp_der_root⟩
        have hp_mult_ge2 : 2 ≤ p.rootMultiplicity x := by lia
        let m : ℕ := p.rootMultiplicity x
        let k : ℕ := m - 2
        obtain ⟨δ, hδ, hqk_not_root⟩ :=
          exists_delta_not_isRoot_iterateTDeriv_at_point k hq_not_root
        let η : ℝ := δ / 2
        have hη_pos : 0 < η := by grind
        have hη_small : ‖η‖ < δ := by
          have hη_norm : ‖η‖ = δ / 2 := by
            rw [Real.norm_eq_abs, show η = δ / 2 by lia, abs_of_pos hη_pos]
          simp_all
        have hqk_not_root_x : ¬ (iterateTDeriv η k q).IsRoot x := hqk_not_root hη_small
        have hqk_eval_ne : (iterateTDeriv η k q).eval x ≠ 0 := by simp_all
        have hk_le : k ≤ p.rootMultiplicity x := by lia
        have hpk_mult :
            (iterateTDeriv η k p).rootMultiplicity x = 2 := by
          calc
            (iterateTDeriv η k p).rootMultiplicity x = p.rootMultiplicity x - k :=
              rootMultiplicity_iterateTDeriv_eq_tsub hη_pos hp_rr.1 hp_rr.2 hk_le
            _ = 2 := by lia
        have hpq_all_k :
            AllComboRealRooted (iterateTDeriv η k p) (iterateTDeriv η k q) :=
          allComboRealRooted_iterateTDeriv hpq_all hη_pos k
        exact
          ObreschkoffConverseInternal.false_of_allComboRealRooted_of_double_root_and_eval_ne
            hpq_all_k hpk_mult hqk_eval_ne
      exact
        ObreschkoffConverseInternal.combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
          hall hW_ne
  have htransport :
      (f.natDegree + 1 = g.natDegree → Prec f g) ∧
        (f.natDegree = g.natDegree → Prec f g ∨ Prec g f) := by
    constructor
    · intro hsucc
      have hprec_or :
          Prec f g ∨ Prec g f :=
        ObreschkoffConverseInternal.prec_of_eq_zero_or_simple_combo_of_no_common
          hf.1 hf.2 hg.1 hg.2 hcombo_original (Or.inl hsucc) hno
      exact prec_forward_of_orientation_of_succDegree hsucc.symm hprec_or
    · intro hsame
      exact
        ObreschkoffConverseInternal.prec_of_eq_zero_or_simple_combo_of_no_common
          hf.1 hf.2 hg.1 hg.2 hcombo_original (Or.inr hsame) hno
  lia
end
end RealRooted
