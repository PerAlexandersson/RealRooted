import RealRooted.MaWang.Weak.Regularization

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Weak-sign Liu--Wang same-degree theorem in the no-common-roots regime. -/
theorem prec_of_interlaces_evalCoeff_nonpos_same_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  let F : ℝ[X] := a * f + b * g
  have hgf' : Interlaces g f := hgf
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hF : (F ≠ 0 ∧ F.Splits) := by
    apply isRealRooted_of_interlaces_evalCoeff_nonpos_of_no_common
      hgf' hg_pos hF_pos
    all_goals simp_all
  set ts := F.roots.sort (· ≤ ·)
  have hts_eq : (↑ts : Multiset ℝ) = F.roots := Multiset.sort_eq ..
  have hts_sorted : ts.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [show ts = F.roots.sort (· ≤ ·) by lia, Multiset.length_sort, card_roots_of_splits hF.2]
  have hoff : ts.length = rs.length + 0 := by lia
  have hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂ := by
    intro pre r₁ r₂ rest hEq
    exact lt_of_consecutive_of_interlaces_of_no_common hf.1 hg.1
      hrs_eq hss_eq hint hEq hno
  have hgsign :=
    eval_sign_of_interlaces_root hg.1 hg.2 hg_pos hrs_sorted hrs_eq hss_eq hint hno
  have hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + 1 →
        F.IsRoot r := by
    intro pre r rest hEq hcount
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    have hroot_nonpos : F.eval r * g.eval r ≤ 0 := by
      simpa [F] using
        eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
          hr_root (hb_nonpos r hr_root)
    exact isRoot_of_eq_max_countP_le_of_sign hF.2 hF_pos hts_eq hoff
      hroot_nonpos (hgsign pre hEq).1 (hgsign pre hEq).2 hEq hcount
  have hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + 1 :=
    countP_le_of_eq_max_isRoot hF.1 hts_eq hoff hstrict hroot_on_max
  have hlt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· < r) ≤ pre.length :=
    countP_lt_of_eq_max_isRoot (rs := rs) (off := 0)
      hF.1 hts_eq hcount_le hroot_on_max
  have hle :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        pre.length < ts.countP (· ≤ r₂) := by
    intro pre r₁ r₂ rest hEq
    induction pre using List.reverseRecOn generalizing r₁ r₂ rest with
    | nil =>
        have hEq_next : rs = ([r₁] : List ℝ) ++ r₂ :: rest := by simp_all
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
          simpa [F] using
            eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
              hr₂_root (hb_nonpos r₂ hr₂_root)
        by_contra hnot
        have hcount_r₂ : ts.countP (· ≤ r₂) = 0 := by simp_all
        have hrs_len : rs.length = rest.length + 2 := by simp_all
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          lia
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign [r₁] hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by grind
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF.2 hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign [r₁] hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by grind
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF.2 hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          simp_all
        grind
    | append_singleton pre x ih =>
        have hEq_prev : rs = pre ++ x :: r₁ :: r₂ :: rest := by simp_all
        have hprev : pre.length < ts.countP (· ≤ r₁) := ih hEq_prev
        have hlen_pre : (pre ++ [x]).length = pre.length + 1 := by simp
        by_cases hgood : (pre ++ [x]).length < ts.countP (· ≤ r₂)
        · lia
        · have hbad : ts.countP (· ≤ r₂) ≤ pre.length + 1 := by lia
          have hr₁_lt_r₂ : r₁ < r₂ := hstrict (pre ++ [x]) hEq
          have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) :=
            List.countP_mono_left <| by
              grind
          have hcount_r₁ : ts.countP (· ≤ r₁) = pre.length + 1 := by lia
          have hcount_r₂ : ts.countP (· ≤ r₂) = pre.length + 1 := by lia
          have hEq_next : rs = ((pre ++ [x]) ++ [r₁]) ++ r₂ :: rest := by simp_all
          have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
          have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
            simpa [F] using
              eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
                hr₂_root (hb_nonpos r₂ hr₂_root)
          have hrs_len : rs.length = pre.length + rest.length + 3 := by grind
          have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
            have hsplit := countP_le_add_countP_gt_eq_length ts r₂
            lia
          have hr₂_Froot : F.IsRoot r₂ := by
            rcases Nat.even_or_odd rest.length with heven | hodd
            · have hF_nonpos : F.eval r₂ ≤ 0 := by
                have hg_pos' : 0 < g.eval r₂ := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).1 heven
                nlinarith [hFg₂_nonpos, hg_pos']
              have hcount_even : Even (ts.countP (r₂ < ·)) := by grind
              exact isRoot_of_eval_nonpos_of_even_countP_gt hF.2 hF_pos hts_eq hF_nonpos
                hcount_even
            · have hF_nonneg : 0 ≤ F.eval r₂ := by
                have hg_neg' : g.eval r₂ < 0 := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).2 hodd
                nlinarith [hFg₂_nonpos, hg_neg']
              have hcount_odd : Odd (ts.countP (r₂ < ·)) := by grind
              exact isRoot_of_eval_nonneg_of_odd_countP_gt hF.2 hF_pos hts_eq hF_nonneg
                hcount_odd
          have hr₂_mem : r₂ ∈ ts := by
            apply Multiset.mem_coe.mp
            simp_all
          have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
            apply countP_lt_countP_of_exists
            · grind
            · exact hr₂_mem
            · simp [not_le_of_gt hr₁_lt_r₂]
            · simp
          lia
  simpa [F] using
    prec_of_count_bounds_same hf.1 hf.2 hF.1 hF.2 hrs_sorted hts_sorted hrs_eq hts_eq hdeg hlt hle

/-- Weak-sign Liu--Wang differ-by-1 theorem in the no-common-roots regime. -/
theorem prec_of_interlaces_evalCoeff_nonpos_succ_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  let F : ℝ[X] := a * f + b * g
  have hgf' : Interlaces g f := hgf
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hF : (F ≠ 0 ∧ F.Splits) := by
    apply isRealRooted_of_interlaces_evalCoeff_nonpos_of_no_common
      hgf' hg_pos hF_pos
    all_goals simp_all
  set ts := F.roots.sort (· ≤ ·)
  have hts_eq : (↑ts : Multiset ℝ) = F.roots := Multiset.sort_eq ..
  have hts_sorted : ts.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [show ts = F.roots.sort (· ≤ ·) by lia, Multiset.length_sort, card_roots_of_splits hF.2]
  have hoff : ts.length = rs.length + 1 := by lia
  have hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂ := by
    intro pre r₁ r₂ rest hEq
    exact lt_of_consecutive_of_interlaces_of_no_common hf.1 hg.1
      hrs_eq hss_eq hint hEq hno
  have hgsign :=
    eval_sign_of_interlaces_root hg.1 hg.2 hg_pos hrs_sorted hrs_eq hss_eq hint hno
  have hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + 2 →
        F.IsRoot r := by
    intro pre r rest hEq hcount
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    have hroot_nonpos : F.eval r * g.eval r ≤ 0 := by
      simpa [F] using
        eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
          hr_root (hb_nonpos r hr_root)
    exact isRoot_of_eq_max_countP_le_of_sign hF.2 hF_pos hts_eq hoff
      hroot_nonpos (hgsign pre hEq).1 (hgsign pre hEq).2 hEq hcount
  have hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + 2 :=
    countP_le_of_eq_max_isRoot hF.1 hts_eq hoff hstrict hroot_on_max
  have hlt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· < r) ≤ pre.length + 1 :=
    countP_lt_of_eq_max_isRoot (rs := rs) (off := 1)
      hF.1 hts_eq hcount_le hroot_on_max
  have hhead :
      ∀ {r : ℝ} {rest : List ℝ},
        rs = r :: rest →
        0 < ts.countP (· ≤ r) := by
    intro r rest hEq
    have hEq' : rs = ([] : List ℝ) ++ r :: rest := by simp_all
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq'
    have hFg_nonpos : F.eval r * g.eval r ≤ 0 := by
      simpa [F] using
        eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
          hr_root (hb_nonpos r hr_root)
    by_contra hnot
    have hcount_r : ts.countP (· ≤ r) = 0 := by lia
    have hrs_len' : rs.length = rest.length + 1 := by simp_all
    have hcount_gt : ts.countP (r < ·) = rest.length + 2 := by
      have hsplit := countP_le_add_countP_gt_eq_length ts r
      lia
    have hr_Froot : F.IsRoot r := by
      rcases Nat.even_or_odd rest.length with heven | hodd
      · have hF_nonpos : F.eval r ≤ 0 := by
          have hg_pos' : 0 < g.eval r := (hgsign [] hEq).1 heven
          nlinarith [hFg_nonpos, hg_pos']
        have hcount_even : Even (ts.countP (r < ·)) := by grind
        exact isRoot_of_eval_nonpos_of_even_countP_gt hF.2 hF_pos hts_eq hF_nonpos
          hcount_even
      · have hF_nonneg : 0 ≤ F.eval r := by
          have hg_neg' : g.eval r < 0 := (hgsign [] hEq).2 hodd
          nlinarith [hFg_nonpos, hg_neg']
        have hcount_odd : Odd (ts.countP (r < ·)) := by grind
        exact isRoot_of_eval_nonneg_of_odd_countP_gt hF.2 hF_pos hts_eq hF_nonneg
          hcount_odd
    have hr_mem : r ∈ ts := by
      apply Multiset.mem_coe.mp
      simp_all
    grind
  have hle :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        pre.length + 1 < ts.countP (· ≤ r₂) := by
    intro pre r₁ r₂ rest hEq
    induction pre using List.reverseRecOn generalizing r₁ r₂ rest with
    | nil =>
        have hEq_head : rs = r₁ :: r₂ :: rest := by simp_all
        have hhead_r₁ : 0 < ts.countP (· ≤ r₁) := hhead hEq_head
        by_contra hnot
        have hbad : ts.countP (· ≤ r₂) ≤ 1 := by simp_all
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict [] hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) :=
          List.countP_mono_left <| by
            grind
        have hcount_r₁ : ts.countP (· ≤ r₁) = 1 := by lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = 1 := by lia
        have hEq_next : rs = ([r₁] : List ℝ) ++ r₂ :: rest := by simp_all
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
          simpa [F] using
            eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
              hr₂_root (hb_nonpos r₂ hr₂_root)
        have hrs_len' : rs.length = rest.length + 2 := by simp_all
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          lia
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign [r₁] hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by grind
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF.2 hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign [r₁] hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by grind
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF.2 hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          simp_all
        have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · grind
          · exact hr₂_mem
          · simp [not_le_of_gt hr₁_lt_r₂]
          · simp
        lia
    | append_singleton pre x ih =>
        have hEq_prev : rs = pre ++ x :: r₁ :: r₂ :: rest := by simp_all
        have hprev : pre.length + 1 < ts.countP (· ≤ r₁) := ih hEq_prev
        have hlen_pre : (pre ++ [x]).length + 1 = pre.length + 2 := by simp
        by_cases hgood : (pre ++ [x]).length + 1 < ts.countP (· ≤ r₂)
        · lia
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict (pre ++ [x]) hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) :=
          List.countP_mono_left <| by
            grind
        have hbad : ts.countP (· ≤ r₂) ≤ pre.length + 2 := by lia
        have hcount_r₁ : ts.countP (· ≤ r₁) = pre.length + 2 := by lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = pre.length + 2 := by lia
        have hEq_next : rs = ((pre ++ [x]) ++ [r₁]) ++ r₂ :: rest := by simp_all
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
          simpa [F] using
            eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
              hr₂_root (hb_nonpos r₂ hr₂_root)
        have : rs.length = pre.length + rest.length + 3 := by grind
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          lia
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by grind
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF.2 hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by grind
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF.2 hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          simp_all
        have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · grind
          · exact hr₂_mem
          · simp [not_le_of_gt hr₁_lt_r₂]
          · simp
        lia
  simpa [F] using
    prec_of_count_bounds_succ hf.1 hf.2 hF.1 hF.2 hrs_sorted
      hts_sorted hrs_eq hts_eq hdeg hhead hlt hle


end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (prec_of_interlaces_evalCoeff_nonpos_same_of_no_common)

end RealRooted
