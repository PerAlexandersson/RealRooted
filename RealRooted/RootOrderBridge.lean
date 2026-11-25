module

public import Mathlib
import RealRooted.RootCountFinite

/-!
# Root-order bridge

This file contains a purely order-theoretic bridge extracted from the
same-degree Chudnovsky--Seymour root-crossing target.
-/

public section

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
        by_cases hh : hd ≤ x
        · cases k with
          | zero => simp [hh]
          | succ k =>
              simpa [hh] using ih htl k (by simpa using hk)
        · have hnone : ∀ y ∈ tl, ¬y ≤ x :=
            fun y hy hyx => hh ((hhd y hy).trans hyx)
          have hf : (tl.filter (· ≤ x)).length = 0 := by
            rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro y hy
            simpa using hnone y hy
          cases k with
          | zero => simp [hh, hf]
          | succ k =>
              have hk' : k < tl.length := by simpa using hk
              have hnot : ¬tl[k]! ≤ x := by
                rw [getElem!_pos tl k hk']
                exact hnone _ (List.getElem_mem hk')
              have hlength : ((hd :: tl).filter (· ≤ x)).length = 0 := by
                simp [hh, hf]
              rw [List.getElem!_cons_succ, hlength]
              exact iff_of_false hnot (Nat.not_lt_zero _)
  convert h_helper s hs x k hk using 1
  aesop (simp_config := { singlePass := true })

/-- The ascending order statistic characterizes a lower-threshold count. -/
private theorem sort_getElem_le_iff {M : Multiset ℝ} (x : ℝ) (i : ℕ) (hi : i < M.card) :
    (M.sort (· ≤ ·))[i]! ≤ x ↔ i < (M.filter (· ≤ x)).card := by
  exact sorted_getElem_le_iff_lt_card_filter _ (Multiset.pairwise_sort _ _)
    M (Multiset.sort_eq _ _) x i (by simpa using hi)

/-- A count bound with arbitrary slack is equivalent to shifted order-statistic bounds. -/
private theorem count_le_iff_sorted_get {M N : Multiset ℝ} {k : ℕ}
    (hcard : M.card ≤ N.card + k) :
    (∀ x : ℝ, (M.filter (· ≤ x)).card ≤ (N.filter (· ≤ x)).card + k) ↔
      ∀ i, k ≤ i → i < M.card →
        (N.sort (· ≤ ·))[i - k]! ≤ (M.sort (· ≤ ·))[i]! := by
  constructor
  · intro hc i hki hi
    have hiN : i - k < N.card := by lia
    have hself := (sort_getElem_le_iff (M := M) _ i hi).mp le_rfl
    have hbound := hc ((M.sort (· ≤ ·))[i]!)
    exact (sort_getElem_le_iff _ (i - k) hiN).mpr (by lia)
  · intro h x
    by_contra hh
    have hM := Multiset.card_le_card (Multiset.filter_le (fun y : ℝ ↦ y ≤ x) M)
    let i := (N.filter (· ≤ x)).card + k
    have hi : i < M.card := by dsimp [i]; lia
    have hki : k ≤ i := by dsimp [i]; lia
    have hiN : i - k < N.card := by lia
    have hMx := (sort_getElem_le_iff (M := M) x i hi).mpr (by dsimp [i]; lia)
    have hNx := (sort_getElem_le_iff (M := N) x (i - k) hiN).mp ((h i hki hi).trans hMx)
    dsimp [i] at hNx
    lia

/-- Reverse lookup uses the complementary ascending index. -/
private theorem reverse_sort_getD (M : Multiset ℝ) (i : ℕ) (hi : i < M.card) :
    (M.sort (· ≤ ·)).reverse.getD i 0 = (M.sort (· ≤ ·))[M.card - 1 - i]! := by
  have hlen : (M.sort (· ≤ ·)).length = M.card := Multiset.length_sort _
  grind

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
  have hleft := (count_le_iff_sorted_get (M := M) (N := N) (k := 1) (by lia)).mp
    (fun x ↦ by have := (hcount x).1; lia)
  have hright := (count_le_iff_sorted_get (M := N) (N := M) (k := 1) (by lia)).mp
    (fun x ↦ by have := (hcount x).2; lia)
  constructor <;> intro j hj₁ hj₂
  · rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)]
    have h₁ : d - 1 - j = d - j - 1 := by lia
    have h₂ : d - 1 - (j - 1) = d - j := by lia
    simpa only [hM, hN, h₁, h₂] using hleft (d - j) (by lia) (by lia)
  · rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)]
    have h₁ : d - 1 - j = d - j - 1 := by lia
    have h₂ : d - 1 - (j - 1) = d - j := by lia
    simpa only [hM, hN, h₁, h₂] using hright (d - j) (by lia) (by lia)

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
  have hleft : ∀ x : ℝ, (M.filter (· ≤ x)).card ≤ (N.filter (· ≤ x)).card + 1 := by
    apply (count_le_iff_sorted_get (by lia)).mpr
    intro i hki hi
    have h := hcross.1 (d - i) (by lia) (by lia)
    rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)] at h
    have h₁ : d - 1 - (d - i) = i - 1 := by lia
    have h₂ : d - 1 - (d - i - 1) = i := by lia
    simpa only [hM, hN, h₁, h₂] using h
  have hright : ∀ x : ℝ, (N.filter (· ≤ x)).card ≤ (M.filter (· ≤ x)).card + 1 := by
    apply (count_le_iff_sorted_get (by lia)).mpr
    intro i hki hi
    have h := hcross.2 (d - i) (by lia) (by lia)
    rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)] at h
    have h₁ : d - 1 - (d - i) = i - 1 := by lia
    have h₂ : d - 1 - (d - i - 1) = i := by lia
    simpa only [hM, hN, h₁, h₂] using h
  intro x
  have := hleft x
  have := hright x
  constructor <;> lia

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
  have hleft : ∀ x : ℝ, (M.filter (· ≤ x)).card ≤ (N.filter (· ≤ x)).card := by
    have h := (count_le_iff_sorted_get (M := M) (N := N) (k := 0) (by lia)).mpr
      (fun i _ hi ↦ ?_)
    · simpa only [Nat.add_zero] using h
    · have h := hcross.1 (d - i) (by lia) (by lia)
      rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)] at h
      have h₁ : d + 1 - 1 - (d - i) = i := by lia
      have h₂ : d - 1 - (d - i - 1) = i := by lia
      simpa only [hM, hN, h₁, h₂, Nat.sub_zero] using h
  have hright : ∀ x : ℝ, (N.filter (· ≤ x)).card ≤ (M.filter (· ≤ x)).card + 2 := by
    apply (count_le_iff_sorted_get (by lia)).mpr
    intro i hki hi
    have h := hcross.2 (d + 1 - i) (by lia) (by lia)
    rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)] at h
    have h₁ : d - 1 - (d + 1 - i) = i - 2 := by lia
    have h₂ : d + 1 - 1 - (d + 1 - i - 1) = i := by lia
    simpa only [hM, hN, h₁, h₂] using h
  intro x
  have := hleft x
  have := hright x
  constructor <;> lia

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
  have hleft := (count_le_iff_sorted_get (M := M) (N := N) (k := 0) (by lia)).mp
    (fun x ↦ by have := (hcount x).1; lia)
  have hright := (count_le_iff_sorted_get (M := N) (N := M) (k := 2) (by lia)).mp
    (fun x ↦ by have := (hcount x).2; lia)
  constructor <;> intro j hj₁ hj₂
  · rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)]
    have h₁ : d + 1 - 1 - j = d - j := by lia
    have h₂ : d - 1 - (j - 1) = d - j := by lia
    simpa only [hM, hN, h₁, h₂, Nat.sub_zero] using hleft (d - j) (by lia) (by lia)
  · rw [reverse_sort_getD _ _ (by lia), reverse_sort_getD _ _ (by lia)]
    have h₁ : d + 1 - j - 2 = d - 1 - j := by lia
    have h₂ : d + 1 - 1 - (j - 1) = d + 1 - j := by lia
    simpa only [hM, hN, h₁, h₂] using hright (d + 1 - j) (by lia) (by lia)

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
