import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RootFilters
import RealRooted.LiuOppositeSigns.Theorem21Statements.NoCommonCrossing.Witnesses

/-!
# Liu x-subtraction adjacent-gap root counts.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- In a left-root gap with no interior left roots, Liu-compatible root counts
allow at most two right roots, counted with multiplicity. -/
theorem RootCountCompatible.card_right_roots_filter_Ioo_le_two_of_left_no_isRoot_Ioo
    {p q : ℝ[X]} (hcount : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {a b : ℝ}
    (hab : a < b)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hqb : ¬ q.IsRoot b) :
    (q.roots.filter (fun r => a < r ∧ r < b)).card ≤ 2 := by
  let P := (p.roots.filter (a < ·)).card
  let Qa := (q.roots.filter (a < ·)).card
  let Qb := (q.roots.filter (b < ·)).card
  let I := (q.roots.filter (fun r => a < r ∧ r < b)).card
  by_cases htwo : 2 ≤ I
  · have hQa_eq : Qa = P + 1 := by
      simpa [P, Qa, I] using
        hcount.card_right_roots_gt_eq_left_roots_gt_add_one_of_left_no_isRoot_Ioo
          hp_ne hq_ne hab hp_no hqb htwo
    have hP_at_b : rootCountAtOrAbove p b = P := by
      have hfilter :
          p.roots.filter (fun r => b ≤ r) = p.roots.filter (a < ·) := by
        apply Multiset.filter_congr
        intro r hr
        constructor
        · intro hbr
          exact lt_of_lt_of_le hab hbr
        · intro har
          by_contra hbr
          exact hp_no r har (lt_of_not_ge hbr)
            ((Polynomial.mem_roots hp_ne).mp hr)
      simp [rootCountAtOrAbove, P, hfilter]
    have hQ_at_b : rootCountAtOrAbove q b = Qb := by
      simpa [Qb] using rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
        hq_ne hqb
    have hP_Qb_le : ((P : ℤ) - Qb) ≤ 1 := by simpa [hP_at_b, hQ_at_b] using (hcount.bounds b).1
    have hq_not_mem_b : b ∉ q.roots := by
      intro hb_mem
      exact hqb ((Polynomial.mem_roots hq_ne).mp hb_mem)
    have hpart : I + Qb = Qa := by
      simpa [I, Qb, Qa] using
        card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
          q.roots (le_of_lt hab) hq_not_mem_b
    have hI_le_int : (I : ℤ) ≤ 2 := by
      have hpart_int : (I : ℤ) + Qb = Qa := by exact_mod_cast hpart
      have hQa_eq_int : (Qa : ℤ) = P + 1 := by exact_mod_cast hQa_eq
      linarith
    exact_mod_cast hI_le_int
  · exact Nat.le_of_not_ge htwo

/-- Odd right-root count in a left-root gap gives at least one root of the
x-subtraction pencil in that gap. -/
theorem NoCommonRoots.one_le_card_xSub_roots_Ioo_of_odd_right_roots
    {p q : ℝ[X]} (hno : NoCommonRoots p q)
    (hq_ne : q ≠ 0) (hq : q.Splits) {a b μ : ℝ}
    (hab : a < b) (ha : p.IsRoot a) (hb : p.IsRoot b)
    (hμ : 0 < μ)
    (hodd : Odd (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    1 ≤ ((X * p - C μ * q).roots.filter
      (fun x => a < x ∧ x < b)).card := by
  have hP_ne : X * p - C μ * q ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  obtain ⟨c, hac, hcb, hc⟩ :=
    hno.exists_isRoot_between_X_mul_sub_C_mul_of_odd_right_roots
      hq_ne hq hab ha hb hμ.ne' hodd
  exact one_le_card_roots_filter_Ioo_of_isRoot hP_ne hac hcb hc

/-- Positive even right-root count in a left-root gap gives at least two roots
of the x-subtraction pencil in that gap. -/
theorem
    PositiveSplitRootCountPair.two_le_card_xSub_roots_Ioo_of_even_right_roots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} (_hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hμ : 0 < μ)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hpos : 0 < (q.roots.filter (fun x => a < x ∧ x < b)).card)
    (heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    2 ≤ ((X * p - C μ * q).roots.filter
      (fun x => a < x ∧ x < b)).card := by
  let s := q.roots.filter (fun x => a < x ∧ x < b)
  have hs_pos : 0 < s.card := by simpa [s] using hpos
  obtain ⟨y, hy_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hs_pos
  have hy_mem' : y ∈ q.roots.filter (fun x => a < x ∧ x < b) := by simpa [s] using hy_mem
  rw [Multiset.mem_filter] at hy_mem'
  obtain ⟨hy_root_mem, ⟨hay, hyb⟩⟩ := hy_mem'
  have hy : q.IsRoot y :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hy_root_mem
  have hP_ne : X * p - C μ * q ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  obtain ⟨c₁, c₂, hac₁, hc₁y, hyc₂, hc₂b, hc₁, hc₂⟩ :=
    hpair.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
      hp_nonneg hno hay hyb ha hb hy hμ hp_no heven
  exact two_le_card_roots_filter_Ioo_of_two_isRoot_ordered
    hP_ne hac₁ (lt_trans hc₁y hyc₂) hc₂b hc₁ hc₂

/-- Local root-count transfer for a left-root gap: Liu-compatible root counts
and the odd/even x-subtraction witnesses give at least
`min 2` as many x-subtraction roots as right roots in the gap. -/
theorem PositiveSplitRootCountPair.min_two_card_right_roots_le_card_xSub_roots_Ioo
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hμ : 0 < μ)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z) :
    min 2 (q.roots.filter (fun x => a < x ∧ x < b)).card ≤
      ((X * p - C μ * q).roots.filter
        (fun x => a < x ∧ x < b)).card := by
  let I := (q.roots.filter (fun x => a < x ∧ x < b)).card
  have hI_le_two : I ≤ 2 := by
    simpa [I] using
      hpair.count.card_right_roots_filter_Ioo_le_two_of_left_no_isRoot_Ioo
        hpair.left_pos.ne_zero hpair.right_pos.ne_zero hab hp_no (hno b hb)
  have hcases : I = 0 ∨ I = 1 ∨ I = 2 := by lia
  rcases hcases with hI | hI | hI
  · simp [I, hI]
  · have hodd : Odd (q.roots.filter (fun x => a < x ∧ x < b)).card := by simp [I, hI]
    have hone :=
      hno.one_le_card_xSub_roots_Ioo_of_odd_right_roots
        hpair.right_pos.ne_zero hpair.right_splits hab ha hb hμ hodd
    simpa [I, hI] using hone
  · have hpos : 0 < (q.roots.filter (fun x => a < x ∧ x < b)).card := by simp [I, hI]
    have heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card := by simp [I, hI]
    have htwo :=
      hpair.two_le_card_xSub_roots_Ioo_of_even_right_roots
        hp_nonneg hno hab ha hb hμ hp_no hpos heven
    simpa [I, hI] using htwo

/-- Adjacent distinct left roots in the sorted root set give the local
`min 2` lower bound for the x-subtraction pencil. -/
theorem PositiveSplitRootCountPair.min_two_card_xSub_Ioo_of_adjacent_left_roots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ}
    (hab_mem : (a, b) ∈ (p.roots.toFinset.sort (· ≤ ·)).zip
      (p.roots.toFinset.sort (· ≤ ·)).tail)
    (hμ : 0 < μ) :
    min 2 (q.roots.filter (fun x => a < x ∧ x < b)).card ≤
      ((X * p - C μ * q).roots.filter
        (fun x => a < x ∧ x < b)).card := by
  let rs := p.roots.toFinset.sort (· ≤ ·)
  have hpair_rs : rs.Pairwise (· < ·) :=
    (Finset.sortedLT_sort p.roots.toFinset).pairwise
  have hchain : rs.IsChain (· < ·) := hpair_rs.isChain
  have hab : a < b := by simpa [rs] using List.rel_of_mem_zip_tail_of_isChain hchain hab_mem
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) :=
    List.fst_mem_of_mem_zip hab_mem
  have hb_mem : b ∈ p.roots.toFinset.sort (· ≤ ·) :=
    List.mem_of_mem_tail (List.snd_mem_of_mem_zip hab_mem)
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp ha_mem
  have hb : p.IsRoot b := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at hb_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hb_mem
  have hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z := by
    intro z haz hzb
    exact Polynomial.not_isRoot_Ioo_of_mem_roots_toFinset_sort_zip_tail
      hpair.left_pos.ne_zero hab_mem haz hzb
  exact hpair.min_two_card_right_roots_le_card_xSub_roots_Ioo
    hp_nonneg hno hab ha hb hμ hp_no

/-- Summing over adjacent entries of the sorted distinct left-root list, the
local `min 2` lower bounds for right-root counts transfer to the corresponding
open-interval root counts of the x-subtraction pencil. -/
theorem PositiveSplitRootCountPair.sum_min_two_right_roots_le_sum_xSub_roots_Ioo
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {μ : ℝ} (hμ : 0 < μ) :
    (((p.roots.toFinset.sort (· ≤ ·)).zip
        (p.roots.toFinset.sort (· ≤ ·)).tail).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
      (((p.roots.toFinset.sort (· ≤ ·)).zip
        (p.roots.toFinset.sort (· ≤ ·)).tail).map
        (fun ab => ((X * p - C μ * q).roots.filter
          (fun x => ab.1 < x ∧ x < ab.2)).card)).sum := by
  apply List.sum_le_sum
  intro ab hab
  exact hpair.min_two_card_xSub_Ioo_of_adjacent_left_roots
    hp_nonneg hno hab hμ

/-- The first entry of the sorted distinct root list is a root, and every root
of the polynomial lies weakly above it. -/
lemma isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs) :
    p.IsRoot a ∧ ∀ r ∈ p.roots, a ≤ r := by
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by simp [hrs]
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hp_ne).mp ha_mem
  refine ⟨ha, ?_⟩
  intro r hr
  have hr_mem : r ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [Finset.mem_sort, Multiset.mem_toFinset]
    exact hr
  have hsorted_le : (p.roots.toFinset.sort (· ≤ ·)).SortedLE :=
    (Finset.sortedLT_sort p.roots.toFinset).sortedLE
  simpa [hrs] using hsorted_le.pairwise.head!_le hr_mem

/-- The right endpoint roots are accounted for by the lower exterior tail,
adjacent open gaps, and the strict upper exterior tail.  Each adjacent gap has
at most two right roots, so replacing each gap count by `min 2` still bounds the
right natural degree from above. -/
theorem
    PositiveSplitRootCountPair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs) :
    q.natDegree ≤
      (q.roots.filter (fun r => r < a)).card +
        (((a :: xs).zip xs).map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (q.roots.filter
          (fun x => (a :: xs).getLast (List.cons_ne_nil a xs) < x)).card := by
  let gaps := (a :: xs).zip xs
  let lowerTail := (q.roots.filter (fun r => r < a)).card
  let plainGapSum :=
    (gaps.map
      (fun ab => (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let minGapSum :=
    (gaps.map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let upperTail :=
    (q.roots.filter
      (fun x => (a :: xs).getLast (List.cons_ne_nil a xs) < x)).card
  have hchain : (a :: xs).IsChain (· < ·) := by
    have hpair_rs :
        (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort p.roots.toFinset).pairwise
    have hchain_rs : (p.roots.toFinset.sort (· ≤ ·)).IsChain (· < ·) :=
      hpair_rs.isChain
    simpa [hrs] using hchain_rs
  have hnode : ∀ x ∈ a :: xs, x ∉ q.roots := by
    intro x hx hxq
    have hx_mem : x ∈ p.roots.toFinset.sort (· ≤ ·) := by
      rw [hrs]
      exact hx
    have hpx : p.IsRoot x := by
      rw [Finset.mem_sort, Multiset.mem_toFinset] at hx_mem
      exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hx_mem
    have hqx : q.IsRoot x :=
      (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hxq
    exact (hno x hpx) hqx
  have hpartition :=
    card_filter_lt_add_sum_card_filter_Ioo_zip_tail_add_card_filter_gt_getLast_eq_card
      (s := q.roots) hchain hnode
  have hplain_le_min : plainGapSum ≤ minGapSum := by
    apply List.sum_le_sum
    intro ab hab
    rcases ab with ⟨u, v⟩
    have hab_sort : (u, v) ∈ (p.roots.toFinset.sort (· ≤ ·)).zip
        (p.roots.toFinset.sort (· ≤ ·)).tail := by
      simpa [gaps, hrs] using hab
    have huv_lt : u < v :=
      List.rel_of_mem_zip_tail_of_isChain hchain (by simpa [gaps] using hab)
    have hv_mem : v ∈ p.roots.toFinset.sort (· ≤ ·) :=
      List.mem_of_mem_tail (List.snd_mem_of_mem_zip hab_sort)
    have hv : p.IsRoot v := by
      rw [Finset.mem_sort, Multiset.mem_toFinset] at hv_mem
      exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hv_mem
    have hp_no : ∀ z : ℝ, u < z → z < v → ¬ p.IsRoot z := by
      intro z huz hzv
      exact Polynomial.not_isRoot_Ioo_of_mem_roots_toFinset_sort_zip_tail
        hpair.left_pos.ne_zero hab_sort huz hzv
    have hgap_le_two :
        (q.roots.filter (fun x => u < x ∧ x < v)).card ≤ 2 :=
      hpair.count.card_right_roots_filter_Ioo_le_two_of_left_no_isRoot_Ioo
        hpair.left_pos.ne_zero hpair.right_pos.ne_zero huv_lt hp_no (hno v hv)
    rw [Nat.min_eq_right hgap_le_two]
  have hq_part : lowerTail + plainGapSum + upperTail = q.natDegree := by
    rw [← card_roots_of_splits hpair.right_splits]
    simpa [lowerTail, plainGapSum, upperTail, gaps] using hpartition
  rw [← hq_part]
  exact Nat.add_le_add (Nat.add_le_add le_rfl hplain_le_min) le_rfl

/-- In the left-successor degree case, the right endpoint roots are accounted
for by the adjacent open gaps and the strict upper exterior tail.  The lower
exterior tail is empty, and each adjacent gap has at most two right roots. -/
theorem
    PositiveSplitRootCountPair.right_natDegree_le_sum_min_two_add_card_right_roots_gt_getLast
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs)
    (hdeg : p.natDegree = q.natDegree + 1) :
    q.natDegree ≤
      (((a :: xs).zip xs).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (q.roots.filter
          (fun x => (a :: xs).getLast (List.cons_ne_nil a xs) < x)).card := by
  have hroots_ge : ∀ r ∈ p.roots, a ≤ r :=
    (isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
      hpair.left_pos.ne_zero hrs).2
  have hlower_zero :
      (q.roots.filter (fun r => r < a)).card = 0 :=
    hpair.card_right_roots_filter_lt_eq_zero_of_left_roots_ge_of_left_natDegree_eq_right_add_one
      hroots_ge hdeg
  have hbound :=
    hpair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
      hno hrs
  simpa [hlower_zero] using hbound

/-- In the same-degree case, the lower exterior right-root tail below the first
left-root threshold transfers into the closed lower tail of the x-subtraction
pencil. -/
theorem PositiveSplitRootCountPair.card_right_roots_lt_head_le_card_xSub_le
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : p.IsRoot a) (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree) (hμ : 0 < μ) :
    (q.roots.filter (fun r => r < a)).card ≤
      ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card := by
  let P := X * p - C μ * q
  let lower := (q.roots.filter (fun r => r < a)).card
  let upper := rootCountAtOrAbove q a
  have hqa : ¬ q.IsRoot a := hno a ha
  have hlower_le_one : lower ≤ 1 := by
    simpa [lower] using
      hpair.card_right_roots_filter_lt_le_one_of_left_roots_ge_of_natDegree_eq
        hroots_ge hdeg
  have hcases : lower = 0 ∨ lower = 1 := by lia
  rcases hcases with hlower | hlower
  · simp [lower, hlower]
  · have hpart : lower + upper = q.natDegree := by
      have hcard := congrArg Multiset.card
        (Multiset.filter_add_not (p := fun r : ℝ => r < a) q.roots)
      have hnot : q.roots.filter (fun r : ℝ => ¬ r < a) =
          q.roots.filter (fun r : ℝ => a ≤ r) := by
        apply Multiset.filter_congr
        intro r _hr
        simp [not_lt]
      rw [Multiset.card_add] at hcard
      simpa [lower, upper, rootCountAtOrAbove, hnot,
        card_roots_of_splits hpair.right_splits] using hcard
    have hP_data :=
      hpair.posLeadingCoeff_and_natDegree_X_mul_sub_C_mul_of_right_natDegree_le
        (by rw [hdeg]) μ
    have hP_pos : HasPosLeadingCoeff P := by simpa [P] using hP_data.1
    have hP_natDegree : P.natDegree = p.natDegree + 1 := by simpa [P] using hP_data.2
    have hP_natDegree_upper : P.natDegree = upper + 2 := by
      rw [hP_natDegree, hdeg]
      lia
    have hP_nat_pos : 0 < P.natDegree := by
      rw [hP_natDegree]
      exact Nat.succ_pos _
    have hP_degree_pos : 0 < P.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp hP_nat_pos
    have hupper_eq :
        upper = (q.roots.filter (a < ·)).card := by
      simpa [upper] using
        rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
          hpair.right_pos.ne_zero hqa
    have hP_ne : P ≠ 0 := hP_pos.ne_zero
    rcases Nat.even_or_odd upper with hupper_even | hupper_odd
    · have hq_a_pos : 0 < q.eval a :=
        (hpair.right_splits.eval_pos_iff_even_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_even)
      have hP_even : Even P.natDegree := by
        rw [hP_natDegree_upper]
        exact hupper_even.add (by norm_num)
      have hbot : Tendsto (fun x => P.eval x) atBot atTop :=
        tendsto_eval_atBot_atTop_of_posLeadingCoeff_even
          hP_pos hP_degree_pos hP_even
      have htail :=
        one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonneg
          ha hq_a_pos.le hμ hP_ne (by simpa [P] using hbot)
      simpa [lower, P, hlower] using htail
    · have hq_a_neg : q.eval a < 0 :=
        (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_odd)
      have hP_odd : Odd P.natDegree := by
        rw [hP_natDegree_upper]
        exact hupper_odd.add_even (by norm_num)
      have hbot : Tendsto (fun x => P.eval x) atBot atBot :=
        tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd
          hP_pos hP_degree_pos hP_odd
      have htail :=
        one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonpos
          ha (le_of_lt hq_a_neg) hμ hP_ne (by simpa [P] using hbot)
      simpa [lower, P, hlower] using htail

/-- In the right-successor degree case, if the lower exterior right-root tail
below the first left root has size two, then the x-subtraction pencil has at
least one root in the closed lower tail. -/
theorem
    PositiveSplitRootCountPair.one_le_card_xSub_le_of_card_right_roots_lt_head_eq_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hq_nonneg : HasNonnegCoeffs q) (hno : NoCommonRoots p q)
    {a μ : ℝ}
    (ha : p.IsRoot a) (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hlower :
      (q.roots.filter (fun r => r < a)).card = 2)
    (hμ : 0 < μ) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card := by
  let P := X * p - C μ * q
  let lower := (q.roots.filter (fun r => r < a)).card
  let upper := rootCountAtOrAbove q a
  have hqa : ¬ q.IsRoot a := hno a ha
  have hpart : lower + upper = q.natDegree := by
    have hcard := congrArg Multiset.card
      (Multiset.filter_add_not (p := fun r : ℝ => r < a) q.roots)
    have hnot : q.roots.filter (fun r : ℝ => ¬ r < a) =
        q.roots.filter (fun r : ℝ => a ≤ r) := by
      apply Multiset.filter_congr
      intro r _hr
      simp [not_lt]
    rw [Multiset.card_add] at hcard
    simpa [lower, upper, rootCountAtOrAbove, hnot,
      card_roots_of_splits hpair.right_splits] using hcard
  have hupper_eq :
      upper = (q.roots.filter (a < ·)).card := by
    simpa [upper] using
      rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
        hpair.right_pos.ne_zero hqa
  have hp_upper : p.natDegree = upper + 1 := by
    have hpart' : 2 + upper = q.natDegree := by simpa [lower, hlower] using hpart
    lia
  have hlower_pos : 0 < (q.roots.filter (fun r => r < a)).card := by simp [hlower]
  obtain ⟨y, hy_filter⟩ := Multiset.card_pos_iff_exists_mem.mp hlower_pos
  rw [Multiset.mem_filter] at hy_filter
  obtain ⟨hy_mem, hya⟩ := hy_filter
  have hy : q.IsRoot y :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hy_mem
  have hP_ne : P ≠ 0 := by simpa [P] using hno.xSub_ne_zero_of_left_root ha hμ.ne'
  rcases lt_or_eq_of_le (roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy_mem)
    with hy_neg | hy_zero
  · have hroots_gt_y : ∀ t ∈ p.roots, y < t := by
      intro t ht
      exact lt_of_lt_of_le hya (hroots_ge t ht)
    rcases Nat.even_or_odd upper with hupper_even | hupper_odd
    · have hq_a_pos : 0 < q.eval a :=
        (hpair.right_splits.eval_pos_iff_even_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_even)
      have hp_odd : Odd p.natDegree := by simpa [hp_upper] using Even.add_one hupper_even
      have hp_y_neg : p.eval y < 0 :=
        eval_neg_of_all_roots_gt_of_odd
          hpair.left_pos.ne_zero hpair.left_pos hp_odd hroots_gt_y
      have hP_y_pos : 0 < P.eval y := by
        have hmul : 0 < y * p.eval y := mul_pos_of_neg_of_neg hy_neg hp_y_neg
        simpa [P, eval_X_mul_sub_C_mul_of_right_isRoot hy] using hmul
      have hP_a_neg : P.eval a < 0 := by
        have hmul : 0 < μ * q.eval a := mul_pos hμ hq_a_pos
        have hneg : -(μ * q.eval a) < 0 := by linarith
        simpa [P, eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
      obtain ⟨c, _hyc, hca, hc_root⟩ :=
        exists_isRoot_between_of_eval_mul_neg (p := P) hya
          (mul_neg_of_pos_of_neg hP_y_pos hP_a_neg)
      exact one_le_card_roots_filter_le_of_isRoot hP_ne (le_of_lt hca) hc_root
    · have hq_a_neg : q.eval a < 0 :=
        (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_odd)
      have hp_even : Even p.natDegree := by simpa [hp_upper] using Odd.add_one hupper_odd
      have hp_y_pos : 0 < p.eval y :=
        eval_pos_of_all_roots_gt_of_even
          hpair.left_pos.ne_zero hpair.left_pos hp_even hroots_gt_y
      have hP_y_neg : P.eval y < 0 := by
        have hmul : y * p.eval y < 0 := mul_neg_of_neg_of_pos hy_neg hp_y_pos
        simpa [P, eval_X_mul_sub_C_mul_of_right_isRoot hy] using hmul
      have hP_a_pos : 0 < P.eval a := by
        have hmul : μ * q.eval a < 0 := mul_neg_of_pos_of_neg hμ hq_a_neg
        have hneg : 0 < -(μ * q.eval a) := neg_pos.mpr hmul
        simpa [P, eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
      obtain ⟨c, _hyc, hca, hc_root⟩ :=
        exists_isRoot_between_of_eval_mul_neg (p := P) hya
          (mul_neg_of_neg_of_pos hP_y_neg hP_a_pos)
      exact one_le_card_roots_filter_le_of_isRoot hP_ne (le_of_lt hca) hc_root
  · subst y
    have hP_zero : P.IsRoot (0 : ℝ) := by simp [P, eval_X_mul_sub_C_mul_of_right_isRoot hy]
    exact one_le_card_roots_filter_le_of_isRoot hP_ne (le_of_lt hya) hP_zero

/-- In the right-successor degree case with negative top coefficient, the lower
exterior right-root tail below the first left root transfers completely into
the closed lower tail of the x-subtraction pencil. -/
theorem
    PositiveSplitRootCountPair.card_right_roots_lt_head_le_card_xSub_le_of_top_coeff_neg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a μ : ℝ}
    (ha : p.IsRoot a) (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hcoeff : p.leadingCoeff - μ * q.leadingCoeff < 0)
    (hμ : 0 < μ) :
    (q.roots.filter (fun r => r < a)).card ≤
      ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card := by
  let P := X * p - C μ * q
  let lower := (q.roots.filter (fun r => r < a)).card
  let upper := rootCountAtOrAbove q a
  have hqa : ¬ q.IsRoot a := hno a ha
  have hpart : lower + upper = q.natDegree := by
    have hcard := congrArg Multiset.card
      (Multiset.filter_add_not (p := fun r : ℝ => r < a) q.roots)
    have hnot : q.roots.filter (fun r : ℝ => ¬ r < a) =
        q.roots.filter (fun r : ℝ => a ≤ r) := by
      apply Multiset.filter_congr
      intro r _hr
      simp [not_lt]
    rw [Multiset.card_add] at hcard
    simpa [lower, upper, rootCountAtOrAbove, hnot,
      card_roots_of_splits hpair.right_splits] using hcard
  have hupper_eq :
      upper = (q.roots.filter (a < ·)).card := by
    simpa [upper] using
      rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
        hpair.right_pos.ne_zero hqa
  have hP_natDegree : P.natDegree = q.natDegree := by
    simpa [P] using
      hpair.natDegree_X_mul_sub_C_mul_eq_right_natDegree_of_right_natDegree_eq_left_add_one
        hdeg (ne_of_lt hcoeff)
  have hnegP_pos : HasPosLeadingCoeff (-P) := by
    simpa [P] using
      hpair.hasPosLeadingCoeff_neg_X_mul_sub_C_mul_of_right_natDegree_eq_left_add_one
        hdeg hcoeff
  have hP_ne : P ≠ 0 := by
    intro hzero
    exact hnegP_pos.ne_zero (by simp [hzero])
  have hP_nat_pos : 0 < P.natDegree := by
    rw [hP_natDegree, hdeg]
    exact Nat.succ_pos _
  have hP_degree_pos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hP_nat_pos
  have hL_le : lower ≤ 2 := by
    simpa [lower] using
      hpair.card_right_roots_filter_lt_le_two_of_roots_ge_of_right_successor
        hroots_ge hdeg
  have hcases : lower = 0 ∨ lower = 1 ∨ lower = 2 := by lia
  rcases hcases with hlower | hlower | hlower
  · simp [lower, hlower]
  · have hq_upper : q.natDegree = upper + 1 := by
      have hpart' : 1 + upper = q.natDegree := by simpa [lower, hlower] using hpart
      lia
    rcases Nat.even_or_odd upper with hupper_even | hupper_odd
    · have hq_a_pos : 0 < q.eval a :=
        (hpair.right_splits.eval_pos_iff_even_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_even)
      have hP_odd : Odd P.natDegree := by
        rw [hP_natDegree, hq_upper]
        exact Even.add_one hupper_even
      have hbot : Tendsto (fun x => P.eval x) atBot atTop :=
        tendsto_eval_atBot_atTop_of_neg_posLeadingCoeff_odd
          hnegP_pos hP_degree_pos hP_odd
      have htail :=
        one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonneg
          ha hq_a_pos.le hμ (by simpa [P] using hP_ne) (by simpa [P] using hbot)
      simpa [lower, P, hlower] using htail
    · have hq_a_neg : q.eval a < 0 :=
        (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_odd)
      have hP_even : Even P.natDegree := by
        rw [hP_natDegree, hq_upper]
        exact Odd.add_one hupper_odd
      have hbot : Tendsto (fun x => P.eval x) atBot atBot :=
        tendsto_eval_atBot_atBot_of_neg_posLeadingCoeff_even
          hnegP_pos hP_degree_pos hP_even
      have htail :=
        one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonpos
          ha (le_of_lt hq_a_neg) hμ (by simpa [P] using hP_ne) (by simpa [P] using hbot)
      simpa [lower, P, hlower] using htail
  · have hp_upper : p.natDegree = upper + 1 := by
      have hpart' : 2 + upper = q.natDegree := by simpa [lower, hlower] using hpart
      lia
    have hq_upper : q.natDegree = upper + 2 := by
      have hpart' : 2 + upper = q.natDegree := by simpa [lower, hlower] using hpart
      lia
    have hlower_pos : 0 < (q.roots.filter (fun r => r < a)).card := by simp [lower, hlower]
    obtain ⟨y, hy_filter⟩ := Multiset.card_pos_iff_exists_mem.mp hlower_pos
    rw [Multiset.mem_filter] at hy_filter
    obtain ⟨hy_mem, hya⟩ := hy_filter
    have hy : q.IsRoot y :=
      (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hy_mem
    have ha_mem : a ∈ p.roots :=
      (Polynomial.mem_roots hpair.left_pos.ne_zero).mpr ha
    have ha_nonpos : a ≤ 0 :=
      roots_nonpos_of_hasNonnegCoeffs hp_nonneg a ha_mem
    have hy_neg : y < 0 := lt_of_lt_of_le hya ha_nonpos
    have hroots_gt_y : ∀ t ∈ p.roots, y < t := by
      intro t ht
      exact lt_of_lt_of_le hya (hroots_ge t ht)
    rcases Nat.even_or_odd upper with hupper_even | hupper_odd
    · have hq_a_pos : 0 < q.eval a :=
        (hpair.right_splits.eval_pos_iff_even_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_even)
      have hp_odd : Odd p.natDegree := by
        rw [hp_upper]
        exact Even.add_one hupper_even
      have hp_y_neg : p.eval y < 0 :=
        eval_neg_of_all_roots_gt_of_odd
          hpair.left_pos.ne_zero hpair.left_pos hp_odd hroots_gt_y
      have hP_y_pos : 0 < P.eval y := by
        have hmul : 0 < y * p.eval y := mul_pos_of_neg_of_neg hy_neg hp_y_neg
        simpa [P, eval_X_mul_sub_C_mul_of_right_isRoot hy] using hmul
      have hP_a_neg : P.eval a < 0 := by
        have hmul : 0 < μ * q.eval a := mul_pos hμ hq_a_pos
        have hneg : -(μ * q.eval a) < 0 := by linarith
        simpa [P, eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
      have hP_even : Even P.natDegree := by
        rw [hP_natDegree, hq_upper]
        exact hupper_even.add (by norm_num)
      have hbot : Tendsto (fun x => P.eval x) atBot atBot :=
        tendsto_eval_atBot_atBot_of_neg_posLeadingCoeff_even
          hnegP_pos hP_degree_pos hP_even
      obtain ⟨c₁, hc₁y, hc₁_root⟩ :=
        exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot
          (le_of_lt hP_y_pos) hbot
      obtain ⟨c₂, hyc₂, hc₂a, hc₂_root⟩ :=
        exists_isRoot_between_of_eval_mul_neg (p := P) hya
          (mul_neg_of_pos_of_neg hP_y_pos hP_a_neg)
      have hc₁c₂ : c₁ < c₂ := lt_of_le_of_lt hc₁y hyc₂
      have htwo :=
        two_le_card_roots_filter_le_of_two_isRoot_ordered hP_ne
          hc₁c₂ hc₂a hc₁_root hc₂_root
      simpa [lower, P, hlower] using htwo
    · have hq_a_neg : q.eval a < 0 :=
        (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_odd)
      have hp_even : Even p.natDegree := by
        rw [hp_upper]
        exact Odd.add_one hupper_odd
      have hp_y_pos : 0 < p.eval y :=
        eval_pos_of_all_roots_gt_of_even
          hpair.left_pos.ne_zero hpair.left_pos hp_even hroots_gt_y
      have hP_y_neg : P.eval y < 0 := by
        have hmul : y * p.eval y < 0 := mul_neg_of_neg_of_pos hy_neg hp_y_pos
        simpa [P, eval_X_mul_sub_C_mul_of_right_isRoot hy] using hmul
      have hP_a_pos : 0 < P.eval a := by
        have hmul : μ * q.eval a < 0 := mul_neg_of_pos_of_neg hμ hq_a_neg
        have hneg : 0 < -(μ * q.eval a) := neg_pos.mpr hmul
        simpa [P, eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
      have hP_odd : Odd P.natDegree := by
        rw [hP_natDegree, hq_upper]
        exact hupper_odd.add_even (by norm_num)
      have hbot : Tendsto (fun x => P.eval x) atBot atTop :=
        tendsto_eval_atBot_atTop_of_neg_posLeadingCoeff_odd
          hnegP_pos hP_degree_pos hP_odd
      obtain ⟨c₁, hc₁y, hc₁_root⟩ :=
        exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop
          (le_of_lt hP_y_neg) hbot
      obtain ⟨c₂, hyc₂, hc₂a, hc₂_root⟩ :=
        exists_isRoot_between_of_eval_mul_neg (p := P) hya
          (mul_neg_of_neg_of_pos hP_y_neg hP_a_pos)
      have hc₁c₂ : c₁ < c₂ := lt_of_le_of_lt hc₁y hyc₂
      have htwo :=
        two_le_card_roots_filter_le_of_two_isRoot_ordered hP_ne
          hc₁c₂ hc₂a hc₁_root hc₂_root
      simpa [lower, P, hlower] using htwo

/-- In the left-successor degree case, if `a` is a lowest left-root threshold
and `p` and `q` have no common root at `a`, then every right root lies strictly
above `a`, counted with multiplicity. -/
theorem
    PositiveSplitRootCountPair.card_right_roots_filter_gt_eq_natDegree_of_left_roots_ge
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a : ℝ}
    (ha : p.IsRoot a) (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree + 1) :
    (q.roots.filter (a < ·)).card = q.natDegree := by
  have hlower_zero :
      (q.roots.filter (fun r => r < a)).card = 0 :=
    hpair.card_right_roots_filter_lt_eq_zero_of_left_roots_ge_of_left_natDegree_eq_right_add_one
      hroots_ge hdeg
  have hqa : ¬ q.IsRoot a := hno a ha
  have hq_all_gt : ∀ r ∈ q.roots, a < r := by
    intro r hr
    have hnot_lt : ¬ r < a := by
      intro hra
      have hr_filter : r ∈ q.roots.filter (fun x => x < a) :=
        Multiset.mem_filter.mpr ⟨hr, hra⟩
      have hpos : 0 < (q.roots.filter (fun x => x < a)).card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨r, hr_filter⟩
      rw [hlower_zero] at hpos
      exact Nat.lt_irrefl 0 hpos
    have har : a ≤ r := le_of_not_gt hnot_lt
    have hne : r ≠ a := by
      intro hra
      have hqr : q.IsRoot a := by
        simpa [hra] using (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hr
      exact hqa hqr
    exact lt_of_le_of_ne har (Ne.symm hne)
  have hfilter : q.roots.filter (a < ·) = q.roots :=
    Multiset.filter_eq_self.mpr hq_all_gt
  simp [hfilter, card_roots_of_splits hpair.right_splits]

/-- Summing over adjacent entries of the sorted distinct left-root list, the
local `min 2` lower bounds for the right-root counts are bounded by the
strict-upper root count of the x-subtraction pencil above the first left root.

This is only the interior-gap count; exterior tail intervals are separate
obligations for the final splitting count. -/
theorem PositiveSplitRootCountPair.sum_min_two_le_card_xSub_gt_of_roots_sort_cons
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs) (hμ : 0 < μ) :
    (((a :: xs).zip xs).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
      ((X * p - C μ * q).roots.filter (a < ·)).card := by
  let P := X * p - C μ * q
  let gaps := (a :: xs).zip xs
  have hpoint :
      (gaps.map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
        (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum := by
    simpa [gaps, P, hrs] using
      hpair.sum_min_two_right_roots_le_sum_xSub_roots_Ioo hp_nonneg hno hμ
  have hchain : (a :: xs).IsChain (· < ·) := by
    have hpair_rs :
        (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort p.roots.toFinset).pairwise
    have hchain_rs : (p.roots.toFinset.sort (· ≤ ·)).IsChain (· < ·) :=
      hpair_rs.isChain
    simpa [hrs] using hchain_rs
  have htel :
      (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
        (P.roots.filter (a < ·)).card := by
    simpa [gaps, P] using
      sum_card_filter_Ioo_zip_tail_le_card_filter_gt (s := P.roots) hchain
  exact le_trans hpoint htel

/-- For at least two distinct left-root locations, the summed adjacent-gap
`min 2` lower bounds and the closed upper tail at the last left root fit
disjointly inside the strict-upper root count of the x-subtraction pencil above
the first left root. -/
theorem
    PositiveSplitRootCountPair.sum_min_two_add_card_xSub_ge_last_le_card_xSub_gt_of_roots_sort
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ) :
    (((a :: b :: xs).zip (b :: xs)).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
      ((X * p - C μ * q).roots.filter
        (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card ≤
    ((X * p - C μ * q).roots.filter (a < ·)).card := by
  let P := X * p - C μ * q
  let gaps := (a :: b :: xs).zip (b :: xs)
  have hpoint :
      (gaps.map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
        (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum := by
    simpa [gaps, P, hrs] using
      hpair.sum_min_two_right_roots_le_sum_xSub_roots_Ioo hp_nonneg hno hμ
  have hchain : (a :: b :: xs).IsChain (· < ·) := by
    have hpair_rs :
        (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort p.roots.toFinset).pairwise
    have hchain_rs : (p.roots.toFinset.sort (· ≤ ·)).IsChain (· < ·) :=
      hpair_rs.isChain
    simpa [hrs] using hchain_rs
  have htail :
      (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (P.roots.filter
          (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card ≤
      (P.roots.filter (a < ·)).card := by
    simpa [gaps, P] using
      sum_card_filter_Ioo_zip_tail_add_card_filter_ge_getLast_le_card_filter_gt
        (s := P.roots) hchain
  exact le_trans (Nat.add_le_add hpoint le_rfl) htail

end LiuOppositeSigns
end RealRooted
