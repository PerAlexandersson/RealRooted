import Mathlib
import RealRooted.RootCountFinite
import RealRooted.RootCountHelpers

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

/-- For natural counts, evenness of the integer difference is the same as
evenness of the natural sum. -/
theorem even_int_nat_sub_iff_even_add (m n : ℕ) :
    Even ((m : ℤ) - n) ↔ Even (m + n) := by
  rw [Int.even_sub, Int.even_coe_nat, Int.even_coe_nat, Nat.even_add]

/-- If two lower counts have complementary upper counts and the second total is
one larger, then lower evenness is equivalent to upper oddness. -/
theorem even_add_iff_odd_add_of_add_eq_succ
    {a b u v d : ℕ} (ha : u + a = d) (hb : v + b = d + 1) :
    Even (a + b) ↔ Odd (u + v) := by
  rw [← Nat.not_even_iff_odd]
  constructor
  · intro hab huv
    have hsum : u + v + (a + b) = 2 * d + 1 := by lia
    have htot : Even (u + v + (a + b)) := by
      rw [Nat.even_add]
      exact ⟨fun _ => hab, fun _ => huv⟩
    rw [hsum] at htot
    exact Nat.not_even_two_mul_add_one d htot
  · intro huv
    by_contra hab
    have hsum : u + v + (a + b) = 2 * d + 1 := by lia
    have htot : Even (u + v + (a + b)) := by
      rw [Nat.even_add]
      exact ⟨fun hu => False.elim (huv hu), fun ha => False.elim (hab ha)⟩
    rw [hsum] at htot
    exact Nat.not_even_two_mul_add_one d htot

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

set_option linter.flexible false in
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
  have hint1 : ∀ i, i + 1 < d → sN[i]! ≤ sM[i + 1]! := by
    intro i hi
    have hstep := hcross.1 (d - 1 - i) (by lia) (by lia)
    rw [h_reverse_getD _ hsN _ (by lia), h_reverse_getD _ hsM _ (by lia)] at hstep
    have e1 : d - 1 - (d - 1 - i) = i := by lia
    have e2 : d - 1 - (d - 1 - i - 1) = i + 1 := by lia
    rw [e1, e2] at hstep
    exact hstep
  have hint2 : ∀ i, i + 1 < d → sM[i]! ≤ sN[i + 1]! := by
    intro i hi
    have hstep := hcross.2 (d - 1 - i) (by lia) (by lia)
    rw [h_reverse_getD _ hsM _ (by lia), h_reverse_getD _ hsN _ (by lia)] at hstep
    have e1 : d - 1 - (d - 1 - i) = i := by lia
    have e2 : d - 1 - (d - 1 - i - 1) = i + 1 := by lia
    rw [e1, e2] at hstep
    exact hstep
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
      rw [h_helper sM hM_sorted M hsM_eq x ((N.filter (· ≤ x)).card + 1) (by lia)]
      lia
    have hNb : sN[(N.filter (· ≤ x)).card]! ≤ x :=
      le_trans (hint1 _ hb1_lt_d) hbx
    have hlt :=
      (h_helper sN hN_sorted N hsN_eq x (N.filter (· ≤ x)).card (by lia)).mp hNb
    lia
  have hba1 : (N.filter (· ≤ x)).card ≤ (M.filter (· ≤ x)).card + 1 := by
    by_contra hcon
    push Not at hcon
    have ha1_lt_d : (M.filter (· ≤ x)).card + 1 < d := by lia
    have hax : sN[(M.filter (· ≤ x)).card + 1]! ≤ x := by
      rw [h_helper sN hN_sorted N hsN_eq x ((M.filter (· ≤ x)).card + 1) (by lia)]
      lia
    have hMa : sM[(M.filter (· ≤ x)).card]! ≤ x :=
      le_trans (hint2 _ ha1_lt_d) hax
    have hlt :=
      (h_helper sM hM_sorted M hsM_eq x (M.filter (· ≤ x)).card (by lia)).mp hMa
    lia
  exact ⟨by lia, by lia⟩

/-- Absolute-value form of `count_diff_le_one_of_rootCrossing`. -/
theorem abs_count_le_sub_le_one_of_rootCrossing
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
      |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card| ≤ 1 := by
  intro x
  obtain ⟨h1, h2⟩ := count_diff_le_one_of_rootCrossing hM hN hcross x
  rw [abs_le]
  exact ⟨by lia, h1⟩

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
  have hpartM := Multiset.card_filter_le_add_card_filter_gt M x
  have hpartN := Multiset.card_filter_le_add_card_filter_gt N x
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
  have hpartM := Multiset.card_filter_le_add_card_filter_gt M x
  have hpartN := Multiset.card_filter_le_add_card_filter_gt N x
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
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) :=
  succRootCrossing_of_count_le_two hM hN
    (count_le_two_of_count_gt_diff_le_one hM hN hcount)

/-- Split a below-`b` count into a below-`a` count and the half-open interval
slot `(a, b]`. -/
theorem card_filter_le_eq_card_filter_le_add_card_filter_Ioc
    (M : Multiset ℝ) {a b : ℝ} (hab : a ≤ b) :
    (M.filter (· ≤ a)).card + (M.filter (fun y => a < y ∧ y ≤ b)).card
      = (M.filter (· ≤ b)).card := by
  have h := Multiset.filter_add_not (p := fun y : ℝ => y ≤ a) (M.filter (· ≤ b))
  rw [Multiset.filter_filter, Multiset.filter_filter] at h
  have e1 : (M.filter fun c => c ≤ a ∧ c ≤ b) = M.filter (· ≤ a) := by
    apply Multiset.filter_congr
    intro y _
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      exact ⟨h, le_trans h hab⟩
  have e2 :
      (M.filter fun c => ¬ c ≤ a ∧ c ≤ b) =
        M.filter (fun y => a < y ∧ y ≤ b) := by
    apply Multiset.filter_congr
    intro y _
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨not_le.mp ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨not_le.mpr ha, hb⟩
  rw [e1, e2] at h
  rw [← h, Multiset.card_add]

/-- Same-cardinality root crossing gives the upper-threshold count bound. -/
theorem count_gt_diff_le_one_of_rootCrossing
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
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1 :=
  count_gt_diff_le_one_of_count_le_diff_le_one hM hN
    (count_diff_le_one_of_rootCrossing hM hN hcross)

/-- Bundled signed lower/upper count bounds from same-cardinality root crossing. -/
theorem count_le_and_gt_diff_le_one_of_rootCrossing
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
      (((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 1 ∧
        ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 1) ∧
      (((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
        ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :=
  fun x =>
    ⟨count_diff_le_one_of_rootCrossing hM hN hcross x,
      count_gt_diff_le_one_of_rootCrossing hM hN hcross x⟩

/-- Absolute-value form of `count_gt_diff_le_one_of_rootCrossing`. -/
theorem abs_count_gt_sub_le_one_of_rootCrossing
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
      |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤ 1 := by
  intro x
  obtain ⟨h1, h2⟩ := count_gt_diff_le_one_of_rootCrossing hM hN hcross x
  rw [abs_le]
  exact ⟨by linarith, h1⟩

/-- Bundled lower/upper absolute-value form of root crossing. -/
theorem abs_count_le_and_gt_sub_le_one_of_rootCrossing
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
      |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card| ≤ 1 ∧
        |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤ 1 := by
  intro x
  exact ⟨abs_count_le_sub_le_one_of_rootCrossing hM hN hcross x,
    abs_count_gt_sub_le_one_of_rootCrossing hM hN hcross x⟩

/-- Max-form bundled lower/upper absolute-value form of root crossing. -/
theorem max_abs_count_le_and_gt_sub_le_one_of_rootCrossing
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
      max
        |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card|
        |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤ 1 := by
  intro x
  exact max_le
    (abs_count_le_sub_le_one_of_rootCrossing hM hN hcross x)
    (abs_count_gt_sub_le_one_of_rootCrossing hM hN hcross x)

/-- The lower and upper absolute count gaps are each bounded by their common
max, and that max is at most one under root crossing. -/
theorem abs_count_le_and_gt_sub_le_common_max_of_rootCrossing
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
      (|((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card| ≤
          max
            |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card|
            |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ∧
        |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤
          max
            |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card|
            |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card|) ∧
      max
        |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card|
        |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤ 1 := by
  intro x
  exact ⟨⟨le_max_left _ _, le_max_right _ _⟩,
    max_abs_count_le_and_gt_sub_le_one_of_rootCrossing hM hN hcross x⟩

/-- Sum-form absolute count bound under root crossing. -/
theorem add_abs_count_le_and_gt_sub_le_two_of_rootCrossing
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
      |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card| +
          |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤ 2 := by
  intro x
  have hle :=
    max_abs_count_le_and_gt_sub_le_one_of_rootCrossing hM hN hcross x
  exact add_le_add (le_trans (le_max_left _ _) hle) (le_trans (le_max_right _ _) hle)

/-- Bundled sum-form and max-form absolute count bounds under root crossing. -/
theorem add_and_max_abs_count_le_and_gt_sub_of_rootCrossing
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
      |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card| +
          |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤ 2 ∧
      max
        |((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card|
        |((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card| ≤ 1 :=
  fun x =>
    ⟨add_abs_count_le_and_gt_sub_le_two_of_rootCrossing hM hN hcross x,
      max_abs_count_le_and_gt_sub_le_one_of_rootCrossing hM hN hcross x⟩

/-- Strictly-above interval-slot count conversion. -/
theorem card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt
    (M : Multiset ℝ) {a b : ℝ} (hab : a ≤ b) :
    (M.filter (fun y => a < y ∧ y ≤ b)).card + (M.filter (b < ·)).card
      = (M.filter (a < ·)).card := by
  have h := Multiset.filter_add_not (p := fun y : ℝ => y ≤ b) (M.filter (a < ·))
  rw [Multiset.filter_filter, Multiset.filter_filter] at h
  have e1 :
      (M.filter fun c => c ≤ b ∧ a < c) =
        M.filter (fun y => a < y ∧ y ≤ b) := by
    apply Multiset.filter_congr
    intro y _
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  have e2 : (M.filter fun c => ¬ c ≤ b ∧ a < c) = M.filter (b < ·) := by
    apply Multiset.filter_congr
    intro y _
    constructor
    · rintro ⟨hb, _⟩
      exact not_le.mp hb
    · intro hb
      exact ⟨not_le.mpr hb, lt_of_le_of_lt hab hb⟩
  rw [e1, e2] at h
  rw [← h, Multiset.card_add]

/-- Same-cardinality root crossing bounds the count difference in every
half-open interval slot `(a, b]` by two. -/
theorem card_filter_Ioc_diff_le_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2 ∧
      ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (M.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2 := by
  have hgt := count_gt_diff_le_one_of_rootCrossing hM hN hcross
  intro a b hab
  have hMa := card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt M hab
  have hNa := card_filter_gt_eq_card_filter_Ioc_add_card_filter_gt N hab
  have hMaz :
      ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ) + (M.filter (b < ·)).card
        = (M.filter (a < ·)).card := by
    exact_mod_cast hMa
  have hNaz :
      ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ) + (N.filter (b < ·)).card
        = (N.filter (a < ·)).card := by
    exact_mod_cast hNa
  have ha := hgt a
  have hb := hgt b
  constructor <;> lia

/-- Absolute-value form of `card_filter_Ioc_diff_le_two_of_rootCrossing`. -/
theorem abs_card_filter_Ioc_sub_le_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card| ≤ 2 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    card_filter_Ioc_diff_le_two_of_rootCrossing hM hN hcross a b hab
  rw [abs_le]
  exact ⟨by lia, h1⟩

set_option linter.flexible false in
/-- Same-cardinality root crossing bounds the difference of strictly-below
counts by one at every threshold.  This is the strict-`<` analogue of
`count_diff_le_one_of_rootCrossing`, which uses `· ≤ x`. -/
theorem count_lt_diff_le_one_of_rootCrossing
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
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 1 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 1 := by
  intro x
  set sM := M.sort (· ≤ ·)
  set sN := N.sort (· ≤ ·)
  have hsM_sorted : List.Pairwise (· ≤ ·) sM := Multiset.pairwise_sort _ _
  have hsN_sorted : List.Pairwise (· ≤ ·) sN := Multiset.pairwise_sort _ _
  have hsM_len : sM.length = d := by aesop
  have hsN_len : sN.length = d := by aesop
  have hsM_eq : Multiset.ofList sM = M := Multiset.sort_eq M (· ≤ ·)
  have hsN_eq : Multiset.ofList sN = N := Multiset.sort_eq N (· ≤ ·)
  have h_filter_lt (s : List ℝ) (hs : List.Pairwise (· ≤ ·) s) (k : ℕ)
      (hk : k < s.length) :
      s.getD k 0 < x ↔ k < (s.filter (· < x)).length := by
    induction s generalizing k with
    | nil => contradiction
    | cons hd tl ih =>
        rcases k with (_ | k) <;> simp_all +decide [List.pairwise_cons]
        · exact fun y hy hyx => lt_of_le_of_lt (hs.1 y hy) hyx
        · grind +splitImp
  have h_reverse_getD (s : List ℝ) (k : ℕ) (hk : k < s.length) :
      s.reverse.getD k 0 = s.getD (s.length - 1 - k) 0 := by
    grind
  have h_hint1 : ∀ i, i + 1 < d → sN.getD i 0 ≤ sM.getD (i + 1) 0 := by
    grind +splitImp
  have h_hint2 : ∀ i, i + 1 < d → sM.getD i 0 ≤ sN.getD (i + 1) 0 := by
    grind +qlia
  have hM_le : (sM.filter (· < x)).length ≤ d :=
    le_trans (List.length_filter_le _ _) hsM_len.le
  have hN_le : (sN.filter (· < x)).length ≤ d :=
    le_trans (List.length_filter_le _ _) hsN_len.le
  have h_a_le_b_plus_1 :
      (sM.filter (· < x)).length ≤ (sN.filter (· < x)).length + 1 := by
    by_contra h_contra
    have h_b_plus_1_lt_d : (sN.filter (· < x)).length + 1 < d := by
      linarith
    grind +splitImp
  have h_b_le_a_plus_1 :
      (sN.filter (· < x)).length ≤ (sM.filter (· < x)).length + 1 := by
    by_contra h_contra
    have h_a_plus_1_lt_d : (sM.filter (· < x)).length + 1 < d := by
      linarith
    grind +splitImp
  constructor <;> norm_num [← hsM_eq, ← hsN_eq] at * <;> linarith

/-- Split a strictly-below-`b` count into a below-`a` count and the open
interval slot `(a, b)`. -/
theorem card_filter_lt_eq_card_filter_le_add_card_filter_Ioo
    (M : Multiset ℝ) {a b : ℝ} (hab : a < b) :
    (M.filter (· ≤ a)).card + (M.filter (fun y => a < y ∧ y < b)).card
      = (M.filter (· < b)).card := by
  have h := Multiset.filter_add_not (p := fun y : ℝ => y ≤ a) (M.filter (· < b))
  rw [Multiset.filter_filter, Multiset.filter_filter] at h
  have e1 : (M.filter fun c => c ≤ a ∧ c < b) = M.filter (· ≤ a) := by
    apply Multiset.filter_congr
    intro y _
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      exact ⟨h, lt_of_le_of_lt h hab⟩
  have e2 :
      (M.filter fun c => ¬ c ≤ a ∧ c < b) =
        M.filter (fun y => a < y ∧ y < b) := by
    apply Multiset.filter_congr
    intro y _
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨not_le.mp ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨not_le.mpr ha, hb⟩
  rw [e1, e2] at h
  rw [← h, Multiset.card_add]

/-- Same-cardinality root crossing bounds the count difference in every
open interval slot `(a, b)` by two. -/
theorem card_filter_Ioo_diff_le_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card ≤ 2 ∧
      ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (M.filter (fun y => a < y ∧ y < b)).card ≤ 2 := by
  have hle := count_diff_le_one_of_rootCrossing hM hN hcross
  have hlt := count_lt_diff_le_one_of_rootCrossing hM hN hcross
  intro a b hab
  rcases lt_or_eq_of_le hab with hab' | hab'
  · have hMa := card_filter_lt_eq_card_filter_le_add_card_filter_Ioo M hab'
    have hNa := card_filter_lt_eq_card_filter_le_add_card_filter_Ioo N hab'
    have hMaz :
        ((M.filter (· ≤ a)).card : ℤ)
            + (M.filter (fun y => a < y ∧ y < b)).card
          = (M.filter (· < b)).card := by
      exact_mod_cast hMa
    have hNaz :
        ((N.filter (· ≤ a)).card : ℤ)
            + (N.filter (fun y => a < y ∧ y < b)).card
          = (N.filter (· < b)).card := by
      exact_mod_cast hNa
    have ha := hle a
    have hb := hlt b
    constructor <;> lia
  · subst hab'
    have hMe : (M.filter (fun y => a < y ∧ y < a)).card = 0 := by
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro y _ hy
      exact absurd (hy.1.trans hy.2) (lt_irrefl a)
    have hNe : (N.filter (fun y => a < y ∧ y < a)).card = 0 := by
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro y _ hy
      exact absurd (hy.1.trans hy.2) (lt_irrefl a)
    rw [hMe, hNe]
    constructor <;> lia

/-- Absolute-value form of `card_filter_Ioo_diff_le_two_of_rootCrossing`. -/
theorem abs_card_filter_Ioo_sub_le_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card| ≤ 2 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    card_filter_Ioo_diff_le_two_of_rootCrossing hM hN hcross a b hab
  rw [abs_le]
  exact ⟨by lia, h1⟩

/-- Direct #42 root-count support: bundled signed half-open `(a, b]` and open
`(a, b)` interval-slot count bounds under same-cardinality root crossing.  This
combines `card_filter_Ioc_diff_le_two_of_rootCrossing` and
`card_filter_Ioo_diff_le_two_of_rootCrossing` so a downstream no-gap argument
can pull both interval slots from a single call. -/
theorem card_filter_Ioc_and_Ioo_diff_le_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2 ∧
        ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2) ∧
      (((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card ≤ 2 ∧
        ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y < b)).card ≤ 2) :=
  fun a b hab =>
    ⟨card_filter_Ioc_diff_le_two_of_rootCrossing hM hN hcross a b hab,
      card_filter_Ioo_diff_le_two_of_rootCrossing hM hN hcross a b hab⟩

/-- Direct #42 root-count support: bundled absolute-value half-open `(a, b]` and
open `(a, b)` interval-slot count bounds under same-cardinality root crossing.
This is the absolute-value analogue of
`card_filter_Ioc_and_Ioo_diff_le_two_of_rootCrossing`. -/
theorem abs_card_filter_Ioc_and_Ioo_sub_le_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card| ≤ 2 ∧
      |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card| ≤ 2 :=
  fun a b hab =>
    ⟨abs_card_filter_Ioc_sub_le_two_of_rootCrossing hM hN hcross a b hab,
      abs_card_filter_Ioo_sub_le_two_of_rootCrossing hM hN hcross a b hab⟩

/-- Direct #42 root-count support: max-form absolute half-open `(a, b]` and open
`(a, b)` interval-slot count bound under same-cardinality root crossing.  This
is the interval-slot analogue of
`max_abs_count_le_and_gt_sub_le_one_of_rootCrossing`. -/
theorem max_abs_card_filter_Ioc_and_Ioo_sub_le_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      max
        |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card|
        |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card| ≤ 2 :=
  fun a b hab =>
    max_le
      (abs_card_filter_Ioc_sub_le_two_of_rootCrossing hM hN hcross a b hab)
      (abs_card_filter_Ioo_sub_le_two_of_rootCrossing hM hN hcross a b hab)

/-- Direct #42 root-count support: sum-form absolute half-open `(a, b]` and open
`(a, b)` interval-slot count bound under same-cardinality root crossing.  This
is the interval-slot analogue of
`add_abs_count_le_and_gt_sub_le_two_of_rootCrossing`. -/
theorem add_abs_card_filter_Ioc_and_Ioo_sub_le_four_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card| +
      |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card| ≤ 4 :=
  fun a b hab =>
    add_le_add
      (abs_card_filter_Ioc_sub_le_two_of_rootCrossing hM hN hcross a b hab)
      (abs_card_filter_Ioo_sub_le_two_of_rootCrossing hM hN hcross a b hab)

/-- Direct #42 no-gap support: the same-cardinality root-crossing interval-slot
bounds rule out a signed count gap of three in both orientations.  The bound is
`≤ 2`, so this intentionally excludes `3`, not the generally possible gap
`2`. -/
theorem
    int_card_filter_Ioc_and_Ioo_sub_card_filter_ne_three_both_orientations_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ 3 ∧
        ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y ≤ b)).card ≠ 3) ∧
      (((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card ≠ 3 ∧
        ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y < b)).card ≠ 3) := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    abs_card_filter_Ioc_and_Ioo_sub_le_two_of_rootCrossing hM hN hcross a b hab
  rw [abs_le] at h1 h2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro H <;>
    linarith [h1.1, h1.2, h2.1, h2.2]

/-- Direct #42 no-gap support: signed-membership form of the root-crossing
interval-slot bounds.  For both the half-open `(a, b]` slot and the open
`(a, b)` slot, the signed count gap `M - N` lies in `[-2, 2]`. -/
theorem card_filter_Ioc_and_Ioo_sub_card_filter_mem_Icc_neg_two_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card)
          ∈ Set.Icc (-2 : ℤ) 2 ∧
      (((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card)
          ∈ Set.Icc (-2 : ℤ) 2 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    abs_card_filter_Ioc_and_Ioo_sub_le_two_of_rootCrossing hM hN hcross a b hab
  rw [abs_le] at h1 h2
  exact ⟨Set.mem_Icc.mpr h1, Set.mem_Icc.mpr h2⟩

/-- Natural-number `≤ · + 2` form of the interval-slot bounds. -/
theorem card_filter_Ioc_and_Ioo_le_add_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      ((M.filter (fun y => a < y ∧ y ≤ b)).card
            ≤ (N.filter (fun y => a < y ∧ y ≤ b)).card + 2 ∧
        (N.filter (fun y => a < y ∧ y ≤ b)).card
            ≤ (M.filter (fun y => a < y ∧ y ≤ b)).card + 2) ∧
      ((M.filter (fun y => a < y ∧ y < b)).card
            ≤ (N.filter (fun y => a < y ∧ y < b)).card + 2 ∧
        (N.filter (fun y => a < y ∧ y < b)).card
            ≤ (M.filter (fun y => a < y ∧ y < b)).card + 2) := by
  intro a b hab
  obtain ⟨⟨hc1, hc2⟩, ho1, ho2⟩ :=
    card_filter_Ioc_and_Ioo_diff_le_two_of_rootCrossing hM hN hcross a b hab
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> lia

/-- Strict `< 3` absolute-value form of the interval-slot bounds. -/
theorem abs_card_filter_Ioc_and_Ioo_sub_lt_three_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card| < 3 ∧
      |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card| < 3 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    abs_card_filter_Ioc_and_Ioo_sub_le_two_of_rootCrossing hM hN hcross a b hab
  exact ⟨by linarith, by linarith⟩

/-- Absolute-value `≠ 3` form; this deliberately does not exclude gap `2`. -/
theorem abs_card_filter_Ioc_and_Ioo_sub_ne_three_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card| ≠ 3 ∧
      |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card| ≠ 3 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    abs_card_filter_Ioc_and_Ioo_sub_lt_three_of_rootCrossing hM hN hcross a b hab
  exact ⟨by intro H; rw [H] at h1; norm_num at h1,
    by intro H; rw [H] at h2; norm_num at h2⟩

/-- `Finset.Icc (-2) 2` membership form of the interval-slot bounds. -/
theorem card_filter_Ioc_and_Ioo_sub_card_filter_mem_finsetIcc_neg_two_two_of_rootCrossing
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d)
    (hcross :
      (∀ j, 1 ≤ j → j < d →
          ((N.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((M.sort (· ≤ ·)).reverse).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < d →
          ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
            ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)) :
    ∀ a b : ℝ, a ≤ b →
      (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card)
          ∈ Finset.Icc (-2 : ℤ) 2 ∧
      (((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card)
          ∈ Finset.Icc (-2 : ℤ) 2 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    abs_card_filter_Ioc_and_Ioo_sub_le_two_of_rootCrossing hM hN hcross a b hab
  rw [abs_le] at h1 h2
  exact ⟨Finset.mem_Icc.mpr h1, Finset.mem_Icc.mpr h2⟩

/-!
### Succ-degree interval-slot count bridges

The succ-degree endpoint-count route supplies asymmetric threshold bounds:

* `((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0`;
* `((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2`.

The wrappers below convert that endpoint bound (and its strict-`<` companion)
into half-open `(a, b]` and open `(a, b)` interval-slot bounds, in the signed,
absolute, `≠ 3` and `Set.Icc (-2) 2` shapes used downstream by
`CommonInterleaverTwo`.  As with the same-degree wrappers, the valid bound is
`≤ 2`: gap `3` is excluded, gap `2` is *not*.  None of these needs the
cardinality equalities; they are pure endpoint-count arithmetic, so they apply
verbatim to the same-degree endpoint bounds as well. -/

/-- Succ-degree half-open interval-slot bound.  From the asymmetric endpoint
count bound (`M ≤ N` and `N ≤ M + 2` at every `· ≤ x` threshold) the signed
count gap over the half-open slot `(a, b]` is at most `2` in both orientations. -/
theorem succ_card_filter_Ioc_diff_le_two_of_count_le
    {M N : Multiset ℝ}
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ a b : ℝ, a ≤ b →
      ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2 ∧
      ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (M.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2 := by
  intro a b hab
  have hMa := card_filter_le_eq_card_filter_le_add_card_filter_Ioc M hab
  have hNa := card_filter_le_eq_card_filter_le_add_card_filter_Ioc N hab
  have hMaz :
      ((M.filter (· ≤ a)).card : ℤ)
          + (M.filter (fun y => a < y ∧ y ≤ b)).card
        = (M.filter (· ≤ b)).card := by
    exact_mod_cast hMa
  have hNaz :
      ((N.filter (· ≤ a)).card : ℤ)
          + (N.filter (fun y => a < y ∧ y ≤ b)).card
        = (N.filter (· ≤ b)).card := by
    exact_mod_cast hNa
  have ha := hcount a
  have hb := hcount b
  constructor <;> lia

/-- Absolute-value form of `succ_card_filter_Ioc_diff_le_two_of_count_le`. -/
theorem abs_succ_card_filter_Ioc_sub_le_two_of_count_le
    {M N : Multiset ℝ}
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card| ≤ 2 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    succ_card_filter_Ioc_diff_le_two_of_count_le hcount a b hab
  rw [abs_le]
  exact ⟨by lia, h1⟩

/-- No-gap-`3` form of the succ-degree half-open interval slot: the signed count
gap over `(a, b]` is never `3`, in either orientation.  This deliberately does
not exclude gap `2`. -/
theorem succ_card_filter_Ioc_sub_ne_three_of_count_le
    {M N : Multiset ℝ}
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ a b : ℝ, a ≤ b →
      ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ 3 ∧
      ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (M.filter (fun y => a < y ∧ y ≤ b)).card ≠ 3 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    succ_card_filter_Ioc_diff_le_two_of_count_le hcount a b hab
  exact ⟨by lia, by lia⟩

/-- `Set.Icc (-2) 2` membership form of the succ-degree half-open interval
slot. -/
theorem succ_card_filter_Ioc_sub_mem_Icc_neg_two_two_of_count_le
    {M N : Multiset ℝ}
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ a b : ℝ, a ≤ b →
      (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card)
          ∈ Set.Icc (-2 : ℤ) 2 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    succ_card_filter_Ioc_diff_le_two_of_count_le hcount a b hab
  exact Set.mem_Icc.mpr ⟨by lia, h1⟩

/-- Succ-degree open interval-slot bound.  From the asymmetric endpoint count
bounds at both the `· ≤ x` and `· < x` thresholds, the signed count gap over the
open slot `(a, b)` is at most `2` in both orientations.  The strict-`<`
hypothesis controls the upper endpoint `b`, while the `· ≤ ·` hypothesis controls
the lower endpoint `a`. -/
theorem succ_card_filter_Ioo_diff_le_two_of_count_lt_le
    {M N : Multiset ℝ}
    (hle : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    (hlt : ∀ x : ℝ,
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 0 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 2) :
    ∀ a b : ℝ, a ≤ b →
      ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card ≤ 2 ∧
      ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (M.filter (fun y => a < y ∧ y < b)).card ≤ 2 := by
  intro a b hab
  rcases lt_or_eq_of_le hab with hab' | hab'
  · have hMa := card_filter_lt_eq_card_filter_le_add_card_filter_Ioo M hab'
    have hNa := card_filter_lt_eq_card_filter_le_add_card_filter_Ioo N hab'
    have hMaz :
        ((M.filter (· ≤ a)).card : ℤ)
            + (M.filter (fun y => a < y ∧ y < b)).card
          = (M.filter (· < b)).card := by
      exact_mod_cast hMa
    have hNaz :
        ((N.filter (· ≤ a)).card : ℤ)
            + (N.filter (fun y => a < y ∧ y < b)).card
          = (N.filter (· < b)).card := by
      exact_mod_cast hNa
    have ha := hle a
    have hb := hlt b
    constructor <;> lia
  · subst hab'
    have hMe : (M.filter (fun y => a < y ∧ y < a)).card = 0 := by
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro y _ hy
      exact absurd (hy.1.trans hy.2) (lt_irrefl a)
    have hNe : (N.filter (fun y => a < y ∧ y < a)).card = 0 := by
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro y _ hy
      exact absurd (hy.1.trans hy.2) (lt_irrefl a)
    rw [hMe, hNe]
    constructor <;> lia

/-- Absolute-value form of `succ_card_filter_Ioo_diff_le_two_of_count_lt_le`. -/
theorem abs_succ_card_filter_Ioo_sub_le_two_of_count_lt_le
    {M N : Multiset ℝ}
    (hle : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    (hlt : ∀ x : ℝ,
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 0 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 2) :
    ∀ a b : ℝ, a ≤ b →
      |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card| ≤ 2 := by
  intro a b hab
  obtain ⟨h1, h2⟩ :=
    succ_card_filter_Ioo_diff_le_two_of_count_lt_le hle hlt a b hab
  rw [abs_le]
  exact ⟨by lia, h1⟩

/-- Direct #42 succ-degree no-gap support: bundled signed half-open `(a, b]` and
open `(a, b)` interval-slot count bounds from the succ-degree endpoint count
hypotheses, so a downstream no-gap argument can pull both slots from a single
call.  Mirrors `card_filter_Ioc_and_Ioo_diff_le_two_of_rootCrossing` for the
succ-degree route. -/
theorem succ_card_filter_Ioc_and_Ioo_diff_le_two_of_count_lt_le
    {M N : Multiset ℝ}
    (hle : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    (hlt : ∀ x : ℝ,
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 0 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 2) :
    ∀ a b : ℝ, a ≤ b →
      (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2 ∧
        ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y ≤ b)).card ≤ 2) ∧
      (((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card ≤ 2 ∧
        ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y < b)).card ≤ 2) :=
  fun a b hab =>
    ⟨succ_card_filter_Ioc_diff_le_two_of_count_le hle a b hab,
      succ_card_filter_Ioo_diff_le_two_of_count_lt_le hle hlt a b hab⟩

/-!
### Conditional no-gap-two sharpenings of the succ-degree interval slots

The interval-slot bridges above bound each signed count gap over `(a, b]` and
`(a, b)` by `2`.  Excluding the exact gap `2` collapses these to sharp
`≤ 1` / `Int.natAbs ≤ 1` bounds.  The no-gap-two exclusion itself is an explicit
hypothesis in every wrapper below.
-/

/-- Conditional sharpening of the succ-degree half-open slot `(a, b]`. -/
theorem succ_card_filter_Ioc_diff_le_one_of_count_le_of_ne_two
    {M N : Multiset ℝ}
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    {a b : ℝ} (hab : a ≤ b)
    (hne : ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ 2 ∧
        ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y ≤ b)).card ≠ 2) :
    ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≤ 1 ∧
      ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (M.filter (fun y => a < y ∧ y ≤ b)).card ≤ 1 :=
  sub_le_one_and_symm_of_le_two_and_ne_two
    (succ_card_filter_Ioc_diff_le_two_of_count_le hcount a b hab) hne

/-- Absolute-value form of the conditional half-open sharpening. -/
theorem abs_succ_card_filter_Ioc_sub_le_one_of_count_le_of_ne_two
    {M N : Multiset ℝ}
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    {a b : ℝ} (hab : a ≤ b)
    (hne : ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ 2)
    (hne' : ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ -2) :
    |((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
        - (N.filter (fun y => a < y ∧ y ≤ b)).card| ≤ 1 :=
  abs_sub_le_one_of_abs_le_two_of_ne_two_of_ne_neg_two
    (abs_succ_card_filter_Ioc_sub_le_two_of_count_le hcount a b hab) hne hne'

/-- `Int.natAbs` distance form of the conditional half-open sharpening. -/
theorem natAbs_succ_card_filter_Ioc_sub_le_one_of_count_le_of_ne_two
    {M N : Multiset ℝ}
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    {a b : ℝ} (hab : a ≤ b)
    (hne : ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ 2)
    (hne' : ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ -2) :
    (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
        - (N.filter (fun y => a < y ∧ y ≤ b)).card).natAbs ≤ 1 :=
  natAbs_sub_le_one_of_abs_sub_le_one
    (abs_succ_card_filter_Ioc_sub_le_one_of_count_le_of_ne_two hcount hab hne hne')

/-- Conditional sharpening of the succ-degree open slot `(a, b)`. -/
theorem succ_card_filter_Ioo_diff_le_one_of_count_lt_le_of_ne_two
    {M N : Multiset ℝ}
    (hle : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    (hlt : ∀ x : ℝ,
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 0 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 2)
    {a b : ℝ} (hab : a ≤ b)
    (hne : ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card ≠ 2 ∧
        ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y < b)).card ≠ 2) :
    ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card ≤ 1 ∧
      ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (M.filter (fun y => a < y ∧ y < b)).card ≤ 1 :=
  sub_le_one_and_symm_of_le_two_and_ne_two
    (succ_card_filter_Ioo_diff_le_two_of_count_lt_le hle hlt a b hab) hne

/-- Absolute-value form of the conditional open sharpening. -/
theorem abs_succ_card_filter_Ioo_sub_le_one_of_count_lt_le_of_ne_two
    {M N : Multiset ℝ}
    (hle : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    (hlt : ∀ x : ℝ,
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 0 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 2)
    {a b : ℝ} (hab : a ≤ b)
    (hne : ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card ≠ 2)
    (hne' : ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card ≠ -2) :
    |((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
        - (N.filter (fun y => a < y ∧ y < b)).card| ≤ 1 :=
  abs_sub_le_one_of_abs_le_two_of_ne_two_of_ne_neg_two
    (abs_succ_card_filter_Ioo_sub_le_two_of_count_lt_le hle hlt a b hab) hne hne'

/-- `Int.natAbs` distance form of the conditional open sharpening. -/
theorem natAbs_succ_card_filter_Ioo_sub_le_one_of_count_lt_le_of_ne_two
    {M N : Multiset ℝ}
    (hle : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    (hlt : ∀ x : ℝ,
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 0 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 2)
    {a b : ℝ} (hab : a ≤ b)
    (hne : ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card ≠ 2)
    (hne' : ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
          - (N.filter (fun y => a < y ∧ y < b)).card ≠ -2) :
    (((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
        - (N.filter (fun y => a < y ∧ y < b)).card).natAbs ≤ 1 :=
  natAbs_sub_le_one_of_abs_sub_le_one
    (abs_succ_card_filter_Ioo_sub_le_one_of_count_lt_le_of_ne_two
      hle hlt hab hne hne')

/-- Bundled conditional sharpening for both succ-degree slots. -/
theorem succ_card_filter_Ioc_and_Ioo_diff_le_one_of_count_lt_le_of_ne_two
    {M N : Multiset ℝ}
    (hle : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2)
    (hlt : ∀ x : ℝ,
      ((M.filter (· < x)).card : ℤ) - (N.filter (· < x)).card ≤ 0 ∧
      ((N.filter (· < x)).card : ℤ) - (M.filter (· < x)).card ≤ 2)
    {a b : ℝ} (hab : a ≤ b)
    (hneIoc : ((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card ≠ 2 ∧
        ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y ≤ b)).card ≠ 2)
    (hneIoo : ((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card ≠ 2 ∧
        ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y < b)).card ≠ 2) :
    (((M.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y ≤ b)).card ≤ 1 ∧
        ((N.filter (fun y => a < y ∧ y ≤ b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y ≤ b)).card ≤ 1) ∧
      (((M.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (N.filter (fun y => a < y ∧ y < b)).card ≤ 1 ∧
        ((N.filter (fun y => a < y ∧ y < b)).card : ℤ)
            - (M.filter (fun y => a < y ∧ y < b)).card ≤ 1) :=
  ⟨succ_card_filter_Ioc_diff_le_one_of_count_le_of_ne_two hle hab hneIoc,
    succ_card_filter_Ioo_diff_le_one_of_count_lt_le_of_ne_two hle hlt hab hneIoo⟩

end RealRooted
