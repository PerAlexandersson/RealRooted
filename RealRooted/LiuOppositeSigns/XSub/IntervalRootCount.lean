import RealRooted.Mathlib.Data.List.Zip
import RealRooted.LiuOppositeSigns.Theorem21Statements

/-!
# Liu x-subtraction interval root counts

This module converts the odd/even interval witnesses for Liu's x-subtraction
pencil into local lower bounds for the number of roots in a single gap between
consecutive left-endpoint roots.
-/

open Polynomial

namespace Polynomial

/-- Adjacent entries in the sorted distinct root list of a nonzero real
polynomial have no root strictly between them. -/
theorem not_isRoot_Ioo_of_mem_roots_toFinset_sort_zip_tail
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b z : ℝ}
    (hab : (a, b) ∈ (p.roots.toFinset.sort (· ≤ ·)).zip
      (p.roots.toFinset.sort (· ≤ ·)).tail)
    (haz : a < z) (hzb : z < b) :
    ¬ p.IsRoot z := by
  intro hz
  have hpair :
      (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort p.roots.toFinset).pairwise
  have hz_mem : z ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [Finset.mem_sort, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hp_ne).mpr hz
  exact List.not_mem_of_mem_zip_tail_of_pairwise_lt hpair hab haz hzb hz_mem

end Polynomial

namespace RealRooted
namespace LiuOppositeSigns

/-- If `c` is a root of `P` in `(a, b)`, then the filtered root multiset has
cardinality at least one. -/
private lemma one_le_card_roots_filter_Ioo_of_isRoot
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hc : P.IsRoot c) :
    1 ≤ (P.roots.filter (fun r => a < r ∧ r < b)).card := by
  have hmem : c ∈ P.roots.filter (fun r => a < r ∧ r < b) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP_ne).mpr hc, ⟨hac, hcb⟩⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨c, hmem⟩

/-- If `c₁ < c₂` are roots of `P` in `(a, b)`, then the filtered root multiset
has cardinality at least two. -/
private lemma two_le_card_roots_filter_Ioo_of_two_isRoot_ordered
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a b c₁ c₂ : ℝ}
    (hac₁ : a < c₁) (hc₁c₂ : c₁ < c₂) (hc₂b : c₂ < b)
    (hc₁ : P.IsRoot c₁) (hc₂ : P.IsRoot c₂) :
    2 ≤ (P.roots.filter (fun r => a < r ∧ r < b)).card := by
  let s := P.roots.filter (fun r => a < r ∧ r < b)
  have hc₁b : c₁ < b := lt_trans hc₁c₂ hc₂b
  have hac₂ : a < c₂ := lt_trans hac₁ hc₁c₂
  have hc₁_mem : c₁ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₁, ⟨hac₁, hc₁b⟩⟩
  have hc₂_mem : c₂ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₂, ⟨hac₂, hc₂b⟩⟩
  have hc₂_erase : c₂ ∈ s.erase c₁ :=
    (Multiset.mem_erase_of_ne (ne_of_lt hc₁c₂).symm).mpr hc₂_mem
  have hpair_le : ({c₁, c₂} : Multiset ℝ) ≤ s := by
    rw [← Multiset.cons_erase hc₁_mem]
    exact Multiset.cons_le_cons c₁ (Multiset.singleton_le.mpr hc₂_erase)
  have hcard := Multiset.card_le_card hpair_le
  simpa [s] using hcard

/-- The x-subtraction pencil is nonzero when the left endpoint has a root and
the two endpoint polynomials have no common roots. -/
theorem NoCommonRoots.xSub_ne_zero_of_left_root
    {p q : ℝ[X]} (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : p.IsRoot a) (hμ : μ ≠ 0) :
    X * p - C μ * q ≠ 0 := by
  intro hzero
  have hPeval : (X * p - C μ * q).eval a = 0 := by
    rw [hzero]
    simp
  have hprod : -μ * q.eval a = 0 := by
    simpa [eval_X_mul_sub_C_mul_of_left_isRoot ha] using hPeval
  have hqeval : q.eval a = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_left (neg_ne_zero.mpr hμ)
  exact (hno a ha) (by simpa [Polynomial.IsRoot.def] using hqeval)

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
    have hP_Qb_le : ((P : ℤ) - Qb) ≤ 1 := by
      simpa [hP_at_b, hQ_at_b] using (hcount.bounds b).1
    have hq_not_mem_b : b ∉ q.roots := by
      intro hb_mem
      exact hqb ((Polynomial.mem_roots hq_ne).mp hb_mem)
    have hpart : I + Qb = Qa := by
      simpa [I, Qb, Qa] using
        card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
          q.roots (le_of_lt hab) hq_not_mem_b
    have hI_le_int : (I : ℤ) ≤ 2 := by
      have hpart_int : (I : ℤ) + Qb = Qa := by
        exact_mod_cast hpart
      have hQa_eq_int : (Qa : ℤ) = P + 1 := by
        exact_mod_cast hQa_eq
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
  have hs_pos : 0 < s.card := by
    simpa [s] using hpos
  obtain ⟨y, hy_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hs_pos
  have hy_mem' : y ∈ q.roots.filter (fun x => a < x ∧ x < b) := by
    simpa [s] using hy_mem
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
  have hcases : I = 0 ∨ I = 1 ∨ I = 2 := by
    lia
  rcases hcases with hI | hI | hI
  · simp [I, hI]
  · have hodd : Odd (q.roots.filter (fun x => a < x ∧ x < b)).card := by
      simp [I, hI]
    have hone :=
      hno.one_le_card_xSub_roots_Ioo_of_odd_right_roots
        hpair.right_pos.ne_zero hpair.right_splits hab ha hb hμ hodd
    simpa [I, hI] using hone
  · have hpos : 0 < (q.roots.filter (fun x => a < x ∧ x < b)).card := by
      simp [I, hI]
    have heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card := by
      simp [I, hI]
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
  have hab : a < b := by
    simpa [rs] using List.rel_of_mem_zip_tail_of_isChain hchain hab_mem
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
    apply List.sum_le_sum
    intro ab hab
    have hab_mem : ab ∈ (p.roots.toFinset.sort (· ≤ ·)).zip
        (p.roots.toFinset.sort (· ≤ ·)).tail := by
      simpa [gaps, hrs] using hab
    exact hpair.min_two_card_xSub_Ioo_of_adjacent_left_roots
      hp_nonneg hno hab_mem hμ
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

end LiuOppositeSigns
end RealRooted
