import Mathlib

/-!
# Root-order bridge

This file contains a purely order-theoretic bridge extracted from the
same-degree Chudnovsky--Seymour root-crossing target.
-/

namespace RealRooted

/-- For natural counts, oddness of the integer difference is the same as
oddness of the natural sum. This is useful because root-count targets are
stated with integer differences, while sign parity naturally sees sums. -/
theorem odd_int_nat_sub_iff_odd_add (m n : ℕ) :
    Odd ((m : ℤ) - n) ↔ Odd (m + n) := by
  rw [← Int.not_even_iff_odd, ← Nat.not_even_iff_odd]
  rw [Int.even_sub, Int.even_coe_nat, Int.even_coe_nat, Nat.even_add]

set_option linter.flexible false in
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
  have hsM : sM.length = d := by aesop
  have hsN : sN.length = d := by aesop
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_helper (s : List ℝ) (hs : s.Pairwise (· ≤ ·)) (P : Multiset ℝ)
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
          rcases k with _ | k
          · by_cases hdx : hd ≤ x
            · simp [hdx]
            · have hfilter : tl.filter (· ≤ x) = [] := by
                rw [List.filter_eq_nil_iff]
                intro y hy hyx
                exact hdx ((hhd y hy).trans (of_decide_eq_true hyx))
              exact iff_of_false hdx (by simp [hdx, hfilter])
          · have hk_tl : k < tl.length := by simpa using hk
            by_cases hdx : hd ≤ x
            · have ihk := ih htl k hk_tl
              simpa [hdx, Nat.succ_lt_succ_iff] using ihk
            · have hfilter : tl.filter (· ≤ x) = [] := by
                rw [List.filter_eq_nil_iff]
                intro y hy hyx
                exact hdx ((hhd y hy).trans (of_decide_eq_true hyx))
              have hnot : ¬tl[k]! ≤ x := by
                intro hyx
                have hmem : tl[k]! ∈ tl := by
                  rw [getElem!_pos tl k hk_tl]
                  exact List.getElem_mem hk_tl
                exact hdx ((hhd _ hmem).trans hyx)
              exact iff_of_false hnot (by simp [hdx, hfilter])
    convert h_helper s hs x k hk using 1
    aesop (simp_config := { singlePass := true })
  have h_reverse_getD (l : List ℝ) (hl : l.length = d) (i : ℕ) (hi : i < d) :
      l.reverse.getD i 0 = l[d - 1 - i]! := by
    grind +splitIndPred
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
    norm_num at *
    lia

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
  have hsM : sM.length = d := by aesop
  have hsN : sN.length = d + 1 := by aesop
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_helper (s : List ℝ) (hs : s.Pairwise (· ≤ ·)) (P : Multiset ℝ)
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
          rcases k with _ | k
          · by_cases hdx : hd ≤ x
            · simp [hdx]
            · have hfilter : tl.filter (· ≤ x) = [] := by
                rw [List.filter_eq_nil_iff]
                intro y hy hyx
                exact hdx ((hhd y hy).trans (of_decide_eq_true hyx))
              exact iff_of_false hdx (by simp [hdx, hfilter])
          · have hk_tl : k < tl.length := by simpa using hk
            by_cases hdx : hd ≤ x
            · have ihk := ih htl k hk_tl
              simpa [hdx, Nat.succ_lt_succ_iff] using ihk
            · have hfilter : tl.filter (· ≤ x) = [] := by
                rw [List.filter_eq_nil_iff]
                intro y hy hyx
                exact hdx ((hhd y hy).trans (of_decide_eq_true hyx))
              have hnot : ¬tl[k]! ≤ x := by
                intro hyx
                have hmem : tl[k]! ∈ tl := by
                  rw [getElem!_pos tl k hk_tl]
                  exact List.getElem_mem hk_tl
                exact hdx ((hhd _ hmem).trans hyx)
              exact iff_of_false hnot (by simp [hdx, hfilter])
    convert h_helper s hs x k hk using 1
    aesop (simp_config := { singlePass := true })
  have h_reverse_getD (l : List ℝ) (hl : l.length = d) (i : ℕ) (hi : i < d) :
      l.reverse.getD i 0 = l[d - 1 - i]! := by
    have hi' : i < l.reverse.length := by simpa [List.length_reverse, hl] using hi
    have hi'' : d - 1 - i < l.length := by
      rw [hl]
      lia
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rw [getElem!_pos l (d - 1 - i) hi'']
    simp [List.getElem_reverse, hl]
  have h_reverse_getD_succ (l : List ℝ) (hl : l.length = d + 1)
      (i : ℕ) (hi : i < d + 1) :
      l.reverse.getD i 0 = l[d - i]! := by
    have hi' : i < l.reverse.length := by simpa [List.length_reverse, hl] using hi
    have hi'' : d - i < l.length := by
      rw [hl]
      lia
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rw [getElem!_pos l (d - i) hi'']
    simp [List.getElem_reverse, hl]
  constructor
  · intro j hj₁ hj₂
    rw [h_reverse_getD_succ _ hsN _ (by lia), h_reverse_getD _ hsM _ (by lia)]
    have hidx : d - j = d - 1 - (j - 1) := by lia
    rw [hidx]
    rw [h_helper _ hN_sorted _ hsN_eq _ _ (by lia)]
    have := h_helper sM hM_sorted M hsM_eq (sM[d - 1 - (j - 1)]!)
      (d - 1 - (j - 1)) (by lia)
    specialize hcount (sM[d - 1 - (j - 1)]!)
    norm_num at *
    lia
  · intro j hj₁ hj₂
    rw [h_reverse_getD _ hsM _ (by lia), h_reverse_getD_succ _ hsN _ (by lia)]
    set k := d - 1 - j with hk
    have hidx : d - (j - 1) = k + 2 := by lia
    rw [hidx]
    rw [h_helper _ hM_sorted _ hsM_eq _ _ (by lia)]
    have := h_helper sN hN_sorted N hsN_eq (sN[k + 2]!) (k + 2) (by lia)
    specialize hcount (sN[k + 2]!)
    norm_num at *
    lia

/-- The roots below-or-at and strictly above a threshold partition a multiset
of real roots. -/
theorem card_filter_le_add_card_filter_gt (M : Multiset ℝ) (x : ℝ) :
    (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = M.card := by
  have h := congrArg Multiset.card
    (Multiset.filter_add_not (p := fun y : ℝ => y ≤ x) M)
  simpa [Multiset.card_add, not_le] using h

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
  have hpartM := card_filter_le_add_card_filter_gt M x
  have hpartN := card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by
    simpa [hM] using hpartM
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d := by
    simpa [hN] using hpartN
  have hMcardz : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by
    exact_mod_cast hMcard
  have hNcardz : ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d := by
    exact_mod_cast hNcard
  have hupper := hcount x
  constructor <;> lia

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
  have hpartM := card_filter_le_add_card_filter_gt M x
  have hpartN := card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by
    simpa [hM] using hpartM
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d := by
    simpa [hN] using hpartN
  have hMcardz : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by
    exact_mod_cast hMcard
  have hNcardz : ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d := by
    exact_mod_cast hNcard
  have hlower := hcount x
  constructor <;> lia

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
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  exact rootCrossing_of_count_diff_le_one hM hN
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
  have hpartM := card_filter_le_add_card_filter_gt M x
  have hpartN := card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by
    simpa [hM] using hpartM
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d + 1 := by
    simpa [hN] using hpartN
  have hMcardz : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by
    exact_mod_cast hMcard
  have hNcardz :
      ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d + 1 := by
    exact_mod_cast hNcard
  have hupper := hcount x
  constructor <;> lia

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
  have hpartM := card_filter_le_add_card_filter_gt M x
  have hpartN := card_filter_le_add_card_filter_gt N x
  have hMcard : (M.filter (· ≤ x)).card + (M.filter (x < ·)).card = d := by
    simpa [hM] using hpartM
  have hNcard : (N.filter (· ≤ x)).card + (N.filter (x < ·)).card = d + 1 := by
    simpa [hN] using hpartN
  have hMcardz : ((M.filter (· ≤ x)).card : ℤ) + (M.filter (x < ·)).card = d := by
    exact_mod_cast hMcard
  have hNcardz :
      ((N.filter (· ≤ x)).card : ℤ) + (N.filter (x < ·)).card = d + 1 := by
    exact_mod_cast hNcard
  have hlower := hcount x
  constructor <;> lia

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
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  exact succRootCrossing_of_count_le_two hM hN
    (count_le_two_of_count_gt_diff_le_one hM hN hcount)

end RealRooted
