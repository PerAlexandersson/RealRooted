import Mathlib
import RealRooted.RootCountFinite

/-!
# Root-order bridge

This file contains a purely order-theoretic bridge extracted from the
same-degree Chudnovsky--Seymour root-crossing target.
-/

namespace RealRooted

/-- In a sorted list, the `k`-th entry is at most `x` exactly when more than
`k` entries are at most `x`, transported through the corresponding multiset. -/
private theorem sorted_getElem_le_iff_lt_card_filter
    (s : List ℝ) (hs : s.Pairwise (· ≤ ·)) (P : Multiset ℝ)
    (hsP : Multiset.ofList s = P) (x : ℝ) (k : ℕ) (hk : k < s.length) :
    s[k]! ≤ x ↔ k < (P.filter (· ≤ x)).card := by
  have h_helper (s : List ℝ) (hs : s.Pairwise (· ≤ ·)) (x : ℝ) (k : ℕ)
      (hk : k < s.length) : s[k]! ≤ x ↔ k < (s.filter (· ≤ x)).length := by
    induction s generalizing k with
    | nil =>
        simp at hk
    | cons hd tl ih =>
        rw [List.pairwise_cons] at hs
        rcases hs with ⟨hhd, htl⟩
        rcases k with _ | k <;> grind
  convert h_helper s hs x k hk using 1
  aesop (simp_config := { singlePass := true })

/-- For natural counts, oddness of the integer difference is the same as
oddness of the natural sum. This is useful because root-count targets are
stated with integer differences, while sign parity naturally sees sums. -/
theorem odd_int_nat_sub_iff_odd_add (m n : ℕ) :
    Odd ((m : ℤ) - n) ↔ Odd (m + n) := by grind

/-- For natural counts, evenness of the integer difference is the same as
evenness of the natural sum. -/
theorem even_int_nat_sub_iff_even_add (m n : ℕ) :
    Even ((m : ℤ) - n) ↔ Even (m + n) := by grind

/-- If two lower counts have complementary upper counts and the second total is
one larger, then lower evenness is equivalent to upper oddness. -/
theorem even_add_iff_odd_add_of_add_eq_succ
    {a b u v d : ℕ} (ha : u + a = d) (hb : v + b = d + 1) :
    Even (a + b) ↔ Odd (u + v) := by
  grind

/-- If two finite multisets of reals have the same cardinality and their
counting functions differ by at most one at every threshold, then their
descending sorted lists satisfy the two interior crossing inequalities. -/
theorem rootCrossing_of_count_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 1 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 1) :
    (∀ j, 1 ≤ j → j < d →
        ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < d →
        ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  set sM := M.sort (· ≤ ·)
  set sN := N.sort (· ≤ ·)
  have hM_sorted : sM.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hN_sorted : sN.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hsM : sM.length = d := by
    subst hM
    simp_all only [tsub_le_iff_right, Multiset.pairwise_sort, Multiset.length_sort, sM, sN]
  have hsN : sN.length = d := by
    subst hM
    simp_all only [tsub_le_iff_right, Multiset.pairwise_sort, Multiset.length_sort, sM, sN]
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_helper := sorted_getElem_le_iff_lt_card_filter
  have h_reverse_getD (l : List ℝ) (hl : l.length = d) (i : ℕ) (hi : i < d) :
      l.reverse.getD i 0 = l[d - 1 - i]! := by grind
  constructor <;> intros j hj₁ hj₂ <;>
    rw [h_reverse_getD _ hsN _ (by lia), h_reverse_getD _ hsM _ (by lia)]
  · rw [h_helper _ hN_sorted _ hsN_eq _ _ (by lia)]
    have := h_helper sM hM_sorted M hsM_eq (sM[d - 1 - (j - 1)]!)
      (d - 1 - (j - 1)) ?_ <;> norm_num at *
    · specialize hcount (sM[d - 1 - (j - 1)]?.getD default)
      lia
    · lia
  · rw [h_helper _ hM_sorted _ hsM_eq _ _ (by lia)]
    have := hcount (sN[d - 1 - (j - 1)]!)
    have := h_helper sN hN_sorted N hsN_eq (sN[d - 1 - (j - 1)]!)
      (d - 1 - (j - 1)) (by lia)
    grind

/-- Converse of `rootCrossing_of_count_diff_le_one`.

If two finite multisets of reals have the same cardinality and their descending
sorted lists satisfy the two interior crossing inequalities, then their lower
counting functions differ by at most one at every threshold. -/
theorem count_diff_le_one_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 1 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 1 := by
  set sM := M.sort (· ≤ ·)
  set sN := N.sort (· ≤ ·)
  have hM_sorted : sM.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hN_sorted : sN.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hsM : sM.length = d := by
    subst hM
    simp_all only [
      Multiset.pairwise_sort, List.getD_eq_getElem?_getD,
      List.length_reverse, Multiset.length_sort,
      getElem?_pos, List.getElem_reverse, Option.getD_some, sM, sN]
  have hsN : sN.length = d := by
    subst hM
    simp_all only [
      Multiset.pairwise_sort, List.getD_eq_getElem?_getD,
      List.length_reverse, Multiset.length_sort,
      getElem?_pos, List.getElem_reverse, Option.getD_some, sM, sN]
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_helper := sorted_getElem_le_iff_lt_card_filter
  have h_reverse_getD (l : List ℝ) (hl : l.length = d) (i : ℕ) (hi : i < d) :
      l.reverse.getD i 0 = l[d - 1 - i]! := by grind
  have hint1 : ∀ i, i + 1 < d → sN[i]! ≤ sM[i + 1]! := by
    grind
  have hint2 : ∀ i, i + 1 < d → sM[i]! ≤ sN[i + 1]! := by grind
  intro x
  have ha_le_d : (M.filter (· ≤ x)).card ≤ d :=
    hM ▸ Multiset.card_le_card (Multiset.filter_le _ _)
  have hb_le_d : (N.filter (· ≤ x)).card ≤ d :=
    hN ▸ Multiset.card_le_card (Multiset.filter_le _ _)
  have hab1 : (M.filter (· ≤ x)).card ≤ (N.filter (· ≤ x)).card + 1 := by
    by_contra hcon
    push Not at hcon
    have hb1_lt_d : (N.filter (· ≤ x)).card + 1 < d := by lia
    have hbx : sM[(N.filter (· ≤ x)).card + 1]! ≤ x := by
      grind
    have hNb : sN[(N.filter (· ≤ x)).card]! ≤ x :=
      le_trans (hint1 _ hb1_lt_d) hbx
    grind
  have hba1 : (N.filter (· ≤ x)).card ≤ (M.filter (· ≤ x)).card + 1 := by
    by_contra hcon
    push Not at hcon
    have ha1_lt_d : (M.filter (· ≤ x)).card + 1 < d := by lia
    have hax : sN[(M.filter (· ≤ x)).card + 1]! ≤ x := by
      grind
    have hMa : sM[(M.filter (· ≤ x)).card]! ≤ x :=
      le_trans (hint2 _ ha1_lt_d) hax
    grind
  grind

/-- Converse of `succRootCrossing_of_count_le_two`.

If `N` has one more element than `M` and their descending sorted lists satisfy
the successor-degree crossing inequalities, then the lower count for `M` is at
most the lower count for `N`, while the latter is at most two larger. -/
theorem count_le_two_of_succRootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcross :
      (∀ j, 1 ≤ j → j ≤ d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2 := by
  set sM := M.sort (· ≤ ·)
  set sN := N.sort (· ≤ ·)
  have hM_sorted : sM.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hN_sorted : sN.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hsM : sM.length = d := by
    simpa [sM] using hM
  have hsN : sN.length = d + 1 := by
    simpa [sN] using hN
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_helper := sorted_getElem_le_iff_lt_card_filter
  have h_reverse_getD (l : List ℝ) (hl : l.length = d) (i : ℕ) (hi : i < d) :
      l.reverse.getD i 0 = l[d - 1 - i]! := by
    grind
  have h_reverse_getD_succ (l : List ℝ) (hl : l.length = d + 1)
      (i : ℕ) (hi : i < d + 1) :
      l.reverse.getD i 0 = l[d - i]! := by
    simp only [List.getD_eq_getElem?_getD, List.length_reverse, hl,
      getElem?_pos, hi, List.getElem_reverse, Option.getD_some]
    have hidx : d + 1 - 1 - i = d - i := by lia
    have hdi : d - i < l.length := by lia
    simp only [hidx, getElem!_pos, hdi]
  have hint1 : ∀ i, i < d → sN[i]! ≤ sM[i]! := by
    grind
  have hint2 : ∀ i, i + 1 < d → sM[i]! ≤ sN[i + 2]! := by
    intro i hi
    let j := d - 1 - i
    have hj_pos : 1 ≤ j := by
      dsimp [j]
      lia
    have hj_lt : j < d := by
      dsimp [j]
      lia
    have hjN : j - 1 < d + 1 := by lia
    have h := hcross.2 j hj_pos hj_lt
    rw [h_reverse_getD sM hsM j hj_lt,
      h_reverse_getD_succ sN hsN (j - 1) hjN] at h
    have hleft : d - 1 - j = i := by
      dsimp [j]
      lia
    have hright : d - (j - 1) = i + 2 := by
      dsimp [j]
      lia
    simpa only [hleft, hright] using h
  intro x
  have ha_le_d : (M.filter (· ≤ x)).card ≤ d :=
    hM ▸ Multiset.card_le_card (Multiset.filter_le _ _)
  have hb_le_succ : (N.filter (· ≤ x)).card ≤ d + 1 :=
    hN ▸ Multiset.card_le_card (Multiset.filter_le _ _)
  have hab0 : (M.filter (· ≤ x)).card ≤ (N.filter (· ≤ x)).card := by
    by_contra hcon
    push Not at hcon
    have hb_lt_d : (N.filter (· ≤ x)).card < d := by lia
    have hMx : sM[(N.filter (· ≤ x)).card]! ≤ x := by
      grind
    have hNb : sN[(N.filter (· ≤ x)).card]! ≤ x :=
      le_trans (hint1 _ hb_lt_d) hMx
    grind
  have hba2 :
      (N.filter (· ≤ x)).card ≤ (M.filter (· ≤ x)).card + 2 := by
    by_contra hcon
    push Not at hcon
    have ha1_lt_d : (M.filter (· ≤ x)).card + 1 < d := by lia
    have hNx : sN[(M.filter (· ≤ x)).card + 2]! ≤ x := by
      grind
    have hMa : sM[(M.filter (· ≤ x)).card]! ≤ x :=
      le_trans (hint2 _ ha1_lt_d) hNx
    grind
  grind

/-- Succ-degree version of `rootCrossing_of_count_diff_le_one`.

If `N` has one more element than `M`, and at every lower threshold the count
for `M` is at most the count for `N`, while the count for `N` is at most two
more than the count for `M`, then the descending sorted lists satisfy the
succ-degree crossing inequalities. -/
theorem succRootCrossing_of_count_le_two
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    (∀ j, 1 ≤ j → j ≤ d →
        ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < d →
        ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  set sM := M.sort (· ≤ ·)
  set sN := N.sort (· ≤ ·)
  have hM_sorted : sM.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hN_sorted : sN.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hsM : sM.length = d := by
    subst hM
    simp_all only [
      tsub_le_iff_right, zero_add, Nat.cast_le,
      Multiset.pairwise_sort, Multiset.length_sort, sM, sN]
  have hsN : sN.length = d + 1 := by
    subst hM
    simp_all only [
      tsub_le_iff_right, zero_add, Nat.cast_le,
      Multiset.pairwise_sort, Multiset.length_sort, sM, sN]
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_helper := sorted_getElem_le_iff_lt_card_filter
  have h_reverse_getD (l : List ℝ) (hl : l.length = d) (i : ℕ) (hi : i < d) :
      l.reverse.getD i 0 = l[d - 1 - i]! := by
    grind
  have h_reverse_getD_succ (l : List ℝ) (hl : l.length = d + 1)
      (i : ℕ) (hi : i < d + 1) :
      l.reverse.getD i 0 = l[d - i]! := by simp_all
  constructor
  · intro j hj₁ hj₂
    rw [h_reverse_getD_succ _ hsN _ (by lia), h_reverse_getD _ hsM _ (by lia)]
    have hidx : d - j = d - 1 - (j - 1) := by lia
    rw [hidx]
    rw [h_helper _ hN_sorted _ hsN_eq _ _ (by lia)]
    have := h_helper sM hM_sorted M hsM_eq (sM[d - 1 - (j - 1)]!)
      (d - 1 - (j - 1)) (by lia)
    specialize hcount (sM[d - 1 - (j - 1)]!)
    grind
  · intro j hj₁ hj₂
    rw [h_reverse_getD _ hsM _ (by lia), h_reverse_getD_succ _ hsN _ (by lia)]
    set k := d - 1 - j with hk
    have hidx : d - (j - 1) = k + 2 := by lia
    rw [hidx]
    rw [h_helper _ hM_sorted _ hsM_eq _ _ (by lia)]
    have := h_helper sN hN_sorted N hsN_eq (sN[k + 2]!) (k + 2) (by lia)
    specialize hcount (sN[k + 2]!)
    grind

/-- Convert the upper-threshold same-cardinality count bound into the
lower-threshold count bound. -/
theorem count_le_diff_le_one_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 1 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 1 := by
  intro x
  have hpartM := Multiset.card_filter_le_add_card_filter_gt M x
  have hpartN := Multiset.card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by simp_all
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d := by simp_all
  have : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by grind
  have : ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d := by grind
  have hupper := hcount x
  grind

/-- Convert the lower-threshold same-cardinality count bound into the
upper-threshold count bound. -/
theorem count_gt_diff_le_one_of_count_le_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 1 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1 := by
  intro x
  have hpartM := Multiset.card_filter_le_add_card_filter_gt M x
  have hpartN := Multiset.card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by simp_all
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d := by simp_all
  have : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by grind
  have : ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d := by grind
  have hlower := hcount x
  grind

/-- Same-cardinality root crossing from the upper-threshold count bound. -/
theorem rootCrossing_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    (∀ j, 1 ≤ j → j < d →
        ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < d →
        ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) :=
  rootCrossing_of_count_diff_le_one hM hN
    (count_le_diff_le_one_of_count_gt_diff_le_one hM hN hcount)

/-- Convert the upper-threshold succ-degree count bound into the asymmetric
lower-threshold bound. -/
theorem count_le_two_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2 := by
  intro x
  have hpartM := Multiset.card_filter_le_add_card_filter_gt M x
  have hpartN := Multiset.card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by simp_all
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d + 1 := by simp_all
  have : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by grind
  have hNcardz :
      ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d + 1 := by grind
  have hupper := hcount x
  grind

/-- Convert the asymmetric lower-threshold succ-degree count bound into the
upper-threshold count bound. -/
theorem count_gt_diff_le_one_of_count_le_two
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1 := by
  intro x
  have hpartM := Multiset.card_filter_le_add_card_filter_gt M x
  have hpartN := Multiset.card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by simp_all
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d + 1 := by simp_all
  have : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by grind
  have hNcardz :
      ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d + 1 := by grind
  have hlower := hcount x
  grind

/-- Succ-degree root crossing from the more analytic upper-threshold count
bound.

If `N` has one more element than `M`, and at every threshold the numbers of
elements strictly above the threshold differ by at most one, then the
descending sorted lists satisfy the succ-degree crossing inequalities. -/
theorem succRootCrossing_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    (∀ j, 1 ≤ j → j ≤ d →
        ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < d →
        ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) :=
  succRootCrossing_of_count_le_two hM hN
    (count_le_two_of_count_gt_diff_le_one hM hN hcount)

end RealRooted
