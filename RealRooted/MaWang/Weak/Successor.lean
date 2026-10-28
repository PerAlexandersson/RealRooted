module

public import RealRooted.MaWang.Weak.Regularization
import RealRooted.MaWang.StrictSigns.Assembly
import RealRooted.MaWang.StrictSigns.RootSigns
import RealRooted.MaWang.CountBounds
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

public section

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWang

private theorem strictInterl_of_interlaces_eval_mul_nonpos_of_no_common_aux
    {f g F : ℝ[X]} (hgf : Interlaces g f) (hg_pos : HasPosLeadingCoeff g)
    (hF_ne : F ≠ 0) (hF_splits : F.Splits) (hF_pos : HasPosLeadingCoeff F)
    (off : ℕ) (hoff_le : off ≤ 1) (hdeg : F.natDegree = f.natDegree + off)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0) :
    StrictInterl f F := by
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  set ts := F.roots.sort (· ≤ ·)
  have hts_eq : (↑ts : Multiset ℝ) = F.roots := Multiset.sort_eq ..
  have hts_sorted : ts.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, Polynomial.splits_iff_card_roots.mp hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [show ts = F.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
      Polynomial.splits_iff_card_roots.mp hF_splits]
  have hoff : ts.length = rs.length + off := by lia
  have hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest → r₁ < r₂ :=
    fun _ _ _ _ hEq ↦ lt_of_consecutive_of_interlaces_of_no_common hf.1 hg.1
      hrs_eq hss_eq hint hEq hno
  have hgsign :=
    eval_sign_of_interlaces_root hg.1 hg.2 hg_pos hrs_sorted hrs_eq hss_eq hint hno
  have hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + off + 1 →
        F.IsRoot r := by
    intro pre r rest hEq hcount
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    exact isRoot_of_eq_max_countP_le_of_sign hF_splits hF_pos hts_eq hoff
      (hroot_nonpos r hr_root) (hgsign pre hEq).1 (hgsign pre hEq).2 hEq hcount
  have hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + off + 1 :=
    countP_le_of_eq_max_isRoot hF_ne hts_eq hoff hstrict hroot_on_max
  have hlt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· < r) ≤ pre.length + off :=
    countP_lt_of_eq_max_isRoot (rs := rs) hF_ne hts_eq hcount_le hroot_on_max
  have hroot_of_count_gt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (r < ·) = rest.length + 2 →
        F.IsRoot r := by
    intro pre r rest hEq hcount_gt
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    have hFg_nonpos : F.eval r * g.eval r ≤ 0 := hroot_nonpos r hr_root
    rcases Nat.even_or_odd rest.length with heven | hodd
    · have hF_nonpos : F.eval r ≤ 0 := by
        have hg_pos' : 0 < g.eval r := (hgsign pre hEq).1 heven
        nlinarith [hFg_nonpos, hg_pos']
      exact isRoot_of_eval_nonpos_of_even_countP_gt hF_splits hF_pos hts_eq hF_nonpos
        (by grind)
    · have hF_nonneg : 0 ≤ F.eval r := by
        have hg_neg' : g.eval r < 0 := (hgsign pre hEq).2 hodd
        nlinarith [hFg_nonpos, hg_neg']
      exact isRoot_of_eval_nonneg_of_odd_countP_gt hF_splits hF_pos hts_eq hF_nonneg
        (by grind)
  have hfirst :
      ∀ {r : ℝ} {rest : List ℝ},
        rs = r :: rest → off ≤ ts.countP (· ≤ r) := by
    intro r rest hEq
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hoff_le with rfl | rfl
    · simp
    have hEq' : rs = ([] : List ℝ) ++ r :: rest := by simp_all
    by_contra hnot
    have hcount_r : ts.countP (· ≤ r) = 0 := by lia
    have hrs_len' : rs.length = rest.length + 1 := by simp_all
    have hcount_gt : ts.countP (r < ·) = rest.length + 2 := by
      have hsplit := countP_le_add_countP_gt_eq_length ts r
      lia
    have hr_Froot : F.IsRoot r := hroot_of_count_gt [] hEq' hcount_gt
    have hr_mem : r ∈ ts := by
      apply Multiset.mem_coe.mp
      simp_all
    grind
  have hle :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        pre.length + off < ts.countP (· ≤ r₂) := by
    intro pre r₁ r₂ rest hEq
    induction pre using List.reverseRecOn generalizing r₁ r₂ rest with
    | nil =>
        have hEq_head : rs = r₁ :: r₂ :: rest := by simp_all
        have hfirst_r₁ : off ≤ ts.countP (· ≤ r₁) := hfirst hEq_head
        by_contra hnot
        have hbad : ts.countP (· ≤ r₂) ≤ off := by simp_all
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict [] hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) :=
          List.countP_mono_left <| by grind
        have hcount_r₁ : ts.countP (· ≤ r₁) = off := by lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = off := by lia
        have hEq_next : rs = ([r₁] : List ℝ) ++ r₂ :: rest := by simp_all
        have hrs_len' : rs.length = rest.length + 2 := by simp_all
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          lia
        have hr₂_Froot : F.IsRoot r₂ := hroot_of_count_gt [r₁] hEq_next hcount_gt
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
        have hprev : pre.length + off < ts.countP (· ≤ r₁) := ih hEq_prev
        by_cases hgood : (pre ++ [x]).length + off < ts.countP (· ≤ r₂)
        · exact hgood
        have hlen_pre : (pre ++ [x]).length = pre.length + 1 := by simp
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict (pre ++ [x]) hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) :=
          List.countP_mono_left <| by grind
        have hbad : ts.countP (· ≤ r₂) ≤ pre.length + off + 1 := by lia
        have hcount_r₁ : ts.countP (· ≤ r₁) = pre.length + off + 1 := by lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = pre.length + off + 1 := by lia
        have hEq_next : rs = ((pre ++ [x]) ++ [r₁]) ++ r₂ :: rest := by simp_all
        have hrs_len' : rs.length = pre.length + rest.length + 3 := by grind
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          lia
        have hr₂_Froot : F.IsRoot r₂ :=
          hroot_of_count_gt ((pre ++ [x]) ++ [r₁]) hEq_next hcount_gt
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
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hoff_le with rfl | rfl
  · apply strictInterl_of_count_bounds_same hf.1 hf.2 hF_ne hF_splits hrs_sorted
      hts_sorted hrs_eq hts_eq (by simpa using hdeg)
    · intro pre r rest hEq
      simpa using hlt pre hEq
    · intro pre r₁ r₂ rest hEq
      simpa using hle pre hEq
  · apply strictInterl_of_count_bounds_succ hf.1 hf.2 hF_ne hF_splits hrs_sorted
      hts_sorted hrs_eq hts_eq hdeg
    · intro r rest hEq
      simpa using hfirst hEq
    · exact hlt
    · exact hle

/-- Generic weak-sign same-degree theorem: if `g ⊳ f`, `F` is real-rooted with
the same degree as `f`, and at every root of `f` the value `F(r)` has
nonpositive sign relative to `g(r)`, then `f ≺ F`. -/
theorem strictInterl_of_interlaces_eval_mul_nonpos_same_of_no_common
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_ne : F ≠ 0) (hF_splits : F.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0) :
    StrictInterl f F :=
  strictInterl_of_interlaces_eval_mul_nonpos_of_no_common_aux hgf hg_pos hF_ne
    hF_splits hF_pos 0 (by lia) (by simpa using hdeg) hno hroot_nonpos

/-- Generic weak-sign differ-by-1 theorem: if `g ⊳ f`, `F` is real-rooted with
degree `deg(f)+1`, and at every root of `f` the value `F(r)` has nonpositive
sign relative to `g(r)`, then `f ⊳ F`. -/
theorem strictInterl_of_interlaces_eval_mul_nonpos_succ_of_no_common
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_ne : F ≠ 0) (hF_splits : F.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0) :
    StrictInterl f F :=
  strictInterl_of_interlaces_eval_mul_nonpos_of_no_common_aux hgf hg_pos hF_ne
    hF_splits hF_pos 1 (by lia) hdeg hno hroot_nonpos

/-- Degree-bounded generic weak-sign theorem in the no-common-roots regime. -/
theorem strictInterl_of_interlaces_eval_mul_nonpos_of_no_common
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_ne : F ≠ 0) (hF_splits : F.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0) :
    StrictInterl f F := by
  rcases Nat.le_and_le_add_one_iff.mp ⟨hdeg_lo, hdeg_hi⟩ with hsame | hsucc
  · exact
      strictInterl_of_interlaces_eval_mul_nonpos_same_of_no_common
        hgf hg_pos hF_ne hF_splits hF_pos hsame hno hroot_nonpos
  · exact
      strictInterl_of_interlaces_eval_mul_nonpos_succ_of_no_common
        hgf hg_pos hF_ne hF_splits hF_pos hsucc hno hroot_nonpos

end RealRooted.MaWang

namespace RealRooted

export MaWang
  (strictInterl_of_interlaces_eval_mul_nonpos_same_of_no_common
    strictInterl_of_interlaces_eval_mul_nonpos_succ_of_no_common
    strictInterl_of_interlaces_eval_mul_nonpos_of_no_common)

end RealRooted
