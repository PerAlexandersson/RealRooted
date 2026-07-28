import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Count
import Mathlib.Tactic

/-!
# Ordered subset pairs

This module defines the finite set of ordered pairs of `k`-subsets of
`Finset.range n` whose sorted lists are componentwise ordered.  The definition
is intended as the reusable, Mathlib-shaped counting surface for ballot and
Narayana enumeration arguments.
-/

namespace List

private theorem sortedLT_tail {x : ℕ} {xs : List ℕ} (h : (x :: xs).SortedLT) :
    xs.SortedLT :=
  List.Pairwise.sortedLT (List.Pairwise.tail (List.SortedLT.pairwise h))

private theorem countP_eq_zero_of_sortedLT_head_gt
    {x : ℕ} {xs : List ℕ} (hxs : (x :: xs).SortedLT) {t : ℕ} (ht : t < x) :
    (x :: xs).countP (· ≤ t) = 0 := by
  rw [List.countP_eq_zero]
  intro z hz
  have hxz : x ≤ z := by
    rcases List.mem_cons.mp hz with hzx | hzxs
    · rw [hzx]
    · exact le_of_lt ((List.pairwise_cons.mp (List.SortedLT.pairwise hxs)).1 z hzxs)
  have hzt : t < z := lt_of_lt_of_le ht hxz
  simp [Nat.not_le.mpr hzt]

private theorem forall2_le_countP_le
    {xs ys : List ℕ} (hxs : xs.SortedLT) (hys : ys.SortedLT)
    (hxy : List.Forall₂ (· ≤ ·) xs ys) (t : ℕ) :
    ys.countP (· ≤ t) ≤ xs.countP (· ≤ t) := by
  induction hxy with
  | nil => simp
  | cons hxy_head hxy_tail ih =>
      rename_i x y xs ys
      cases hyt : decide (y ≤ t)
      · have hygt : t < y := Nat.lt_of_not_ge (of_decide_eq_false hyt)
        have hzero : (y :: ys).countP (· ≤ t) = 0 :=
          countP_eq_zero_of_sortedLT_head_gt hys hygt
        rw [hzero]
        exact Nat.zero_le _
      · have hyle : y ≤ t := of_decide_eq_true hyt
        have hxle : x ≤ t := hxy_head.trans hyle
        simp only [countP_cons, ge_iff_le, hxle, hyle, decide_true, ↓reduceIte]
        exact Nat.succ_le_succ (ih (sortedLT_tail hxs) (sortedLT_tail hys))

private theorem forall2_le_of_countP_le
    {xs ys : List ℕ} (hxs : xs.SortedLT) (hys : ys.SortedLT)
    (hlen : xs.length = ys.length)
    (hcount : ∀ t : ℕ, ys.countP (· ≤ t) ≤ xs.countP (· ≤ t)) :
    List.Forall₂ (· ≤ ·) xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact List.Forall₂.nil
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail_len : xs.length = ys.length := by
            simpa using Nat.succ.inj hlen
          have hxle_y : x ≤ y := by
            by_contra hnot
            have hyltx : y < x := Nat.lt_of_not_ge hnot
            have hzero : (x :: xs).countP (· ≤ y) = 0 :=
              countP_eq_zero_of_sortedLT_head_gt hxs hyltx
            have hle := hcount y
            rw [hzero] at hle
            have hpos : 0 < (y :: ys).countP (· ≤ y) := by simp
            exact (not_lt_of_ge hle) hpos
          have htail_count : ∀ t : ℕ, ys.countP (· ≤ t) ≤ xs.countP (· ≤ t) := by
            intro t
            cases hyt : decide (y ≤ t)
            · have hygt : t < y := Nat.lt_of_not_ge (of_decide_eq_false hyt)
              have hzero : (y :: ys).countP (· ≤ t) = 0 :=
                countP_eq_zero_of_sortedLT_head_gt hys hygt
              have hy_tail_zero : ys.countP (· ≤ t) = 0 := by
                simpa [countP_cons, hyt] using hzero
              rw [hy_tail_zero]
              exact Nat.zero_le _
            · have hyle : y ≤ t := of_decide_eq_true hyt
              have hxle : x ≤ t := hxle_y.trans hyle
              have hle := hcount t
              simp only [countP_cons, hyle, hxle, decide_true, ↓reduceIte] at hle
              exact Nat.succ_le_succ_iff.mp hle
          exact List.Forall₂.cons hxle_y
            (ih (sortedLT_tail hxs) (sortedLT_tail hys) htail_len htail_count)

/-- For strictly sorted lists of natural numbers with the same length,
componentwise order is equivalent to dominance of all prefix counts. -/
theorem forall₂_le_iff_countP_le
    {xs ys : List ℕ} (hxs : xs.SortedLT) (hys : ys.SortedLT)
    (hlen : xs.length = ys.length) :
    List.Forall₂ (· ≤ ·) xs ys ↔
      ∀ t : ℕ, ys.countP (· ≤ t) ≤ xs.countP (· ≤ t) :=
  ⟨forall2_le_countP_le hxs hys,
    forall2_le_of_countP_le hxs hys hlen⟩

end List

namespace Finset

/-- Prefix-count dominance for finite sets of natural numbers. -/
def prefixDominates (A B : Finset ℕ) : Prop :=
  ∀ i : ℕ, (B.filter fun x => x ≤ i).card ≤ (A.filter fun x => x ≤ i).card

/-- Failing prefix-count dominance means some threshold has strictly more
elements of `B` below it than elements of `A` below it. -/
theorem not_prefixDominates_iff_exists_card_filter_lt {A B : Finset ℕ} :
    ¬ prefixDominates A B ↔
      ∃ i : ℕ, (A.filter fun x => x ≤ i).card < (B.filter fun x => x ≤ i).card := by
  unfold prefixDominates
  push Not
  rfl

/-- The first threshold where `B` has more elements below the threshold than `A`. -/
noncomputable def firstPrefixViolation (A B : Finset ℕ) (h : ¬ prefixDominates A B) : ℕ :=
  Nat.find ((not_prefixDominates_iff_exists_card_filter_lt).mp h)

/-- The first prefix-violation threshold is violating. -/
theorem firstPrefixViolation_spec {A B : Finset ℕ} (h : ¬ prefixDominates A B) :
    (A.filter fun x => x ≤ firstPrefixViolation A B h).card <
      (B.filter fun x => x ≤ firstPrefixViolation A B h).card := by
  exact Nat.find_spec ((not_prefixDominates_iff_exists_card_filter_lt).mp h)

/-- No smaller threshold violates prefix dominance. -/
theorem firstPrefixViolation_min {A B : Finset ℕ} (h : ¬ prefixDominates A B)
    {j : ℕ} (hj : j < firstPrefixViolation A B h) :
    ¬ (A.filter fun x => x ≤ j).card < (B.filter fun x => x ≤ j).card := by
  exact Nat.find_min ((not_prefixDominates_iff_exists_card_filter_lt).mp h) hj

private theorem card_filter_lt_le_of_forall_not_prefix {i : ℕ} {A B : Finset ℕ}
    (hmin : ∀ j < i,
      ¬ (A.filter fun x => x ≤ j).card < (B.filter fun x => x ≤ j).card) :
    (B.filter fun x => x < i).card ≤ (A.filter fun x => x < i).card := by
  cases i with
  | zero => simp
  | succ j =>
      have h := hmin j (Nat.lt_succ_self j)
      rw [not_lt] at h
      simpa [Nat.lt_succ_iff] using h

private theorem card_filter_le_le_card_filter_lt_add_one (i : ℕ) (A : Finset ℕ) :
    (A.filter fun x => x ≤ i).card ≤ (A.filter fun x => x < i).card + 1 := by
  have hdecomp : A.filter (fun x => x ≤ i) =
      (A.filter fun x => x < i) ∪ (A.filter fun x => x = i) := by
    ext x
    constructor
    · intro hx
      rw [mem_filter] at hx
      rw [mem_union, mem_filter, mem_filter]
      rcases lt_or_eq_of_le hx.2 with hlt | heq
      · exact Or.inl ⟨hx.1, hlt⟩
      · exact Or.inr ⟨hx.1, heq⟩
    · intro hx
      rw [mem_union, mem_filter, mem_filter] at hx
      rw [mem_filter]
      rcases hx with ⟨hxA, hlt⟩ | ⟨hxA, rfl⟩
      · exact ⟨hxA, le_of_lt hlt⟩
      · exact ⟨hxA, le_rfl⟩
  calc
    (A.filter fun x => x ≤ i).card
        = ((A.filter fun x => x < i) ∪ (A.filter fun x => x = i)).card := by
          rw [hdecomp]
    _ ≤ (A.filter fun x => x < i).card + (A.filter fun x => x = i).card :=
        card_union_le _ _
    _ ≤ (A.filter fun x => x < i).card + 1 := by
      gcongr
      rw [filter_eq']
      split <;> simp

/-- At the first prefix-violation threshold, the excess is exactly one. -/
theorem firstPrefixViolation_prefix_succ {A B : Finset ℕ} (h : ¬ prefixDominates A B) :
    (B.filter fun x => x ≤ firstPrefixViolation A B h).card =
      (A.filter fun x => x ≤ firstPrefixViolation A B h).card + 1 := by
  let i := firstPrefixViolation A B h
  have hviolate : (A.filter fun x => x ≤ i).card < (B.filter fun x => x ≤ i).card := by
    simpa [i] using firstPrefixViolation_spec h
  have hmin : ∀ j < i,
      ¬ (A.filter fun x => x ≤ j).card < (B.filter fun x => x ≤ j).card := by
    intro j hj
    exact firstPrefixViolation_min h (by simpa [i] using hj)
  have hlt : (B.filter fun x => x < i).card ≤ (A.filter fun x => x < i).card :=
    card_filter_lt_le_of_forall_not_prefix hmin
  have hBstep : (B.filter fun x => x ≤ i).card ≤
      (B.filter fun x => x < i).card + 1 :=
    card_filter_le_le_card_filter_lt_add_one i B
  have hAlt : (A.filter fun x => x < i).card ≤ (A.filter fun x => x ≤ i).card := by
    apply card_le_card
    intro x hx
    exact mem_filter.mpr ⟨(mem_filter.mp hx).1, le_of_lt (mem_filter.mp hx).2⟩
  have hupper : (B.filter fun x => x ≤ i).card ≤
      (A.filter fun x => x ≤ i).card + 1 := by
    calc
      (B.filter fun x => x ≤ i).card ≤ (B.filter fun x => x < i).card + 1 := hBstep
      _ ≤ (A.filter fun x => x < i).card + 1 := Nat.succ_le_succ hlt
      _ ≤ (A.filter fun x => x ≤ i).card + 1 := Nat.succ_le_succ hAlt
  exact le_antisymm hupper (Nat.succ_le_of_lt hviolate)

private theorem filter_le_range_card_eq_self {n : ℕ} {A : Finset ℕ} (hA : A ⊆ range n) :
    A.filter (fun x => x ≤ n) = A := by
  ext x
  constructor
  · intro hx
    exact (mem_filter.mp hx).1
  · intro hx
    exact mem_filter.mpr ⟨hx, le_of_lt (mem_range.mp (hA hx))⟩

/-- If two finite sets are contained in `range n` and `A` is smaller than `B`,
then some prefix has more elements of `B` than of `A`. -/
theorem exists_prefix_lt_of_card_lt_of_subset_range {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range n) (hB : B ⊆ range n) (hcard : A.card < B.card) :
    ∃ i : ℕ, (A.filter fun x => x ≤ i).card < (B.filter fun x => x ≤ i).card := by
  refine ⟨n, ?_⟩
  rw [filter_le_range_card_eq_self hA, filter_le_range_card_eq_self hB]
  exact hcard

/-- Unequal cardinalities inside the same `range n` force failure of prefix dominance. -/
theorem not_prefixDominates_of_card_lt_of_subset_range {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range n) (hB : B ⊆ range n) (hcard : A.card < B.card) :
    ¬ prefixDominates A B := by
  rw [not_prefixDominates_iff_exists_card_filter_lt]
  exact exists_prefix_lt_of_card_lt_of_subset_range hA hB hcard

/-- Exchange the tails of two finite sets of natural numbers after the threshold `i`. -/
def tailExchangeAt (i : ℕ) (A B : Finset ℕ) : Finset ℕ × Finset ℕ :=
  (A.filter (fun x => x ≤ i) ∪ B.filter (fun x => i < x),
    B.filter (fun x => x ≤ i) ∪ A.filter (fun x => i < x))

@[simp] theorem mem_tailExchangeAt_fst {i x : ℕ} {A B : Finset ℕ} :
    x ∈ (tailExchangeAt i A B).1 ↔ (x ∈ A ∧ x ≤ i) ∨ (x ∈ B ∧ i < x) := by
  simp [tailExchangeAt]

@[simp] theorem mem_tailExchangeAt_snd {i x : ℕ} {A B : Finset ℕ} :
    x ∈ (tailExchangeAt i A B).2 ↔ (x ∈ B ∧ x ≤ i) ∨ (x ∈ A ∧ i < x) := by
  simp [tailExchangeAt]

theorem tailExchangeAt_fst_subset_range {n i : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range n) (hB : B ⊆ range n) :
    (tailExchangeAt i A B).1 ⊆ range n := by
  intro x hx
  rw [mem_tailExchangeAt_fst] at hx
  exact hx.elim (fun h => hA h.1) (fun h => hB h.1)

theorem tailExchangeAt_snd_subset_range {n i : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range n) (hB : B ⊆ range n) :
    (tailExchangeAt i A B).2 ⊆ range n := by
  intro x hx
  rw [mem_tailExchangeAt_snd] at hx
  exact hx.elim (fun h => hB h.1) (fun h => hA h.1)

private theorem disjoint_filter_le_filter_gt (i : ℕ) (A B : Finset ℕ) :
    Disjoint (A.filter fun x => x ≤ i) (B.filter fun x => i < x) := by
  rw [disjoint_left]
  intro x hxA hxB
  exact (not_lt_of_ge (mem_filter.mp hxA).2) (mem_filter.mp hxB).2

theorem card_tailExchangeAt_fst (i : ℕ) (A B : Finset ℕ) :
    (tailExchangeAt i A B).1.card =
      (A.filter fun x => x ≤ i).card + (B.filter fun x => i < x).card := by
  rw [tailExchangeAt, card_union_eq_card_add_card]
  exact disjoint_filter_le_filter_gt i A B

theorem card_tailExchangeAt_snd (i : ℕ) (A B : Finset ℕ) :
    (tailExchangeAt i A B).2.card =
      (B.filter fun x => x ≤ i).card + (A.filter fun x => i < x).card := by
  rw [tailExchangeAt, card_union_eq_card_add_card]
  exact disjoint_filter_le_filter_gt i B A

private theorem card_filter_gt_eq_card_sub_card_filter_le (i : ℕ) (A : Finset ℕ) :
    (A.filter fun x => i < x).card = A.card - (A.filter fun x => x ≤ i).card := by
  have h := card_filter_add_card_filter_not (s := A) (p := fun x => x ≤ i)
  have hnot : A.filter (fun x => ¬ x ≤ i) = A.filter fun x => i < x := by
    ext x
    simp
  rw [hnot] at h
  rw [Nat.add_comm] at h
  exact Nat.eq_sub_of_add_eq h

/-- If the `B` prefix at `i` exceeds the `A` prefix by one, the first exchanged
set has one fewer element than `B`. -/
theorem card_tailExchangeAt_fst_of_prefix_succ {i k : ℕ} {A B : Finset ℕ}
    (hBcard : B.card = k)
    (hprefix : (B.filter fun x => x ≤ i).card = (A.filter fun x => x ≤ i).card + 1) :
    (tailExchangeAt i A B).1.card = k - 1 := by
  rw [card_tailExchangeAt_fst, card_filter_gt_eq_card_sub_card_filter_le, hBcard, hprefix]
  have hle : (A.filter fun x => x ≤ i).card + 1 ≤ k := by
    rw [← hprefix, ← hBcard]
    exact card_filter_le _ _
  lia

/-- If the `B` prefix at `i` exceeds the `A` prefix by one, the second exchanged
set has one more element than `A`. -/
theorem card_tailExchangeAt_snd_of_prefix_succ {i k : ℕ} {A B : Finset ℕ}
    (hAcard : A.card = k)
    (hprefix : (B.filter fun x => x ≤ i).card = (A.filter fun x => x ≤ i).card + 1) :
    (tailExchangeAt i A B).2.card = k + 1 := by
  rw [card_tailExchangeAt_snd, card_filter_gt_eq_card_sub_card_filter_le, hAcard, hprefix]
  have hle : (A.filter fun x => x ≤ i).card ≤ k := by
    rw [← hAcard]
    exact card_filter_le _ _
  lia

/-- Exchanging tails at a fixed threshold is an involution. -/
theorem tailExchangeAt_tailExchangeAt (i : ℕ) (A B : Finset ℕ) :
    tailExchangeAt i (tailExchangeAt i A B).1 (tailExchangeAt i A B).2 = (A, B) := by
  ext x <;> by_cases hx : x ≤ i
  · have hxnot : ¬ i < x := not_lt_of_ge hx
    simp [tailExchangeAt, hx, hxnot]
  · have hxgt : i < x := Nat.lt_of_not_ge hx
    simp [tailExchangeAt, hx, hxgt]
  · have hxnot : ¬ i < x := not_lt_of_ge hx
    simp [tailExchangeAt, hx, hxnot]
  · have hxgt : i < x := Nat.lt_of_not_ge hx
    simp [tailExchangeAt, hx, hxgt]

/-- Counting entries of a sorted finset list below a threshold is the same as
filtering the finset by that threshold. -/
theorem countP_sort_eq_card_filter (A : Finset ℕ) (i : ℕ) :
    (A.sort (· ≤ ·)).countP (· ≤ i) = (A.filter fun x => x ≤ i).card := by
  rw [List.countP_eq_length_filter]
  have hnodup : ((A.sort (· ≤ ·)).filter (fun x => x ≤ i)).Nodup :=
    List.Nodup.filter _ (A.sort_nodup (· ≤ ·))
  have hfin : ((A.sort (· ≤ ·)).filter (fun x => x ≤ i)).toFinset =
      A.filter (fun x => x ≤ i) := by
    ext x
    simp
  rw [← List.toFinset_card_of_nodup hnodup, hfin]

/-- The sorted-list componentwise order for two equal-cardinality finsets is
equivalent to prefix-count dominance. -/
theorem forall₂_sort_le_iff_prefixDominates {A B : Finset ℕ}
    (hcard : A.card = B.card) :
    List.Forall₂ (· ≤ ·) (A.sort (· ≤ ·)) (B.sort (· ≤ ·)) ↔
      prefixDominates A B := by
  rw [List.forall₂_le_iff_countP_le (A.sortedLT_sort) (B.sortedLT_sort)]
  · unfold prefixDominates
    simp_rw [countP_sort_eq_card_filter]
  · simp [hcard]

/-- A bad sorted-list pair has a threshold where `B` has more small elements
than `A`. -/
theorem not_forall₂_sort_le_iff_exists_card_filter_lt {A B : Finset ℕ}
    (hcard : A.card = B.card) :
    ¬ List.Forall₂ (· ≤ ·) (A.sort (· ≤ ·)) (B.sort (· ≤ ·)) ↔
      ∃ i : ℕ, (A.filter fun x => x ≤ i).card < (B.filter fun x => x ≤ i).card := by
  rw [forall₂_sort_le_iff_prefixDominates hcard]
  exact not_prefixDominates_iff_exists_card_filter_lt

/-- Pairs of `k`-subsets of `range n` whose sorted lists are componentwise
ordered. -/
def orderedKSubsetPairs (n k : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (((range n).powersetCard k).product ((range n).powersetCard k)).filter fun AB =>
    List.Forall₂ (· ≤ ·) (AB.1.sort (· ≤ ·)) (AB.2.sort (· ≤ ·))

/-- Membership in the ordered `k`-subset-pair finite set. -/
@[simp] theorem mem_orderedKSubsetPairs
    {n k : ℕ} {A B : Finset ℕ} :
    (A, B) ∈ orderedKSubsetPairs n k ↔
      A ⊆ range n ∧ A.card = k ∧ B ⊆ range n ∧ B.card = k ∧
        List.Forall₂ (· ≤ ·) (A.sort (· ≤ ·)) (B.sort (· ≤ ·)) := by
  simp [orderedKSubsetPairs, and_assoc]

/-- Membership in the ordered pair set in terms of prefix-count dominance. -/
theorem mem_orderedKSubsetPairs_iff_prefixDominates
    {n k : ℕ} {A B : Finset ℕ} :
    (A, B) ∈ orderedKSubsetPairs n k ↔
      A ⊆ range n ∧ A.card = k ∧ B ⊆ range n ∧ B.card = k ∧ prefixDominates A B := by
  rw [mem_orderedKSubsetPairs]
  constructor
  · rintro ⟨hA, hAcard, hB, hBcard, hAB⟩
    have hcard : A.card = B.card := by rw [hAcard, hBcard]
    exact ⟨hA, hAcard, hB, hBcard, (forall₂_sort_le_iff_prefixDominates hcard).mp hAB⟩
  · rintro ⟨hA, hAcard, hB, hBcard, hAB⟩
    have hcard : A.card = B.card := by rw [hAcard, hBcard]
    exact ⟨hA, hAcard, hB, hBcard, (forall₂_sort_le_iff_prefixDominates hcard).mpr hAB⟩

/-- There is only the empty ordered pair when `k = 0`. -/
@[simp] theorem orderedKSubsetPairs_zero (n : ℕ) :
    orderedKSubsetPairs n 0 = {((∅ : Finset ℕ), (∅ : Finset ℕ))} := by
  ext AB
  rcases AB with ⟨A, B⟩
  simp only [mem_orderedKSubsetPairs, card_eq_zero, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨_hArange, hAempty, _hBrange, hBempty, _hordered⟩
    exact ⟨hAempty, hBempty⟩
  · rintro ⟨hAempty, hBempty⟩
    subst A
    subst B
    simp

/-- The ordered-pair count is one when `k = 0`. -/
@[simp] theorem card_orderedKSubsetPairs_zero (n : ℕ) :
    (orderedKSubsetPairs n 0).card = 1 := by
  simp

/-- There are no ordered `k`-subset pairs in `range n` when `n < k`. -/
theorem orderedKSubsetPairs_eq_empty_of_lt {n k : ℕ} (h : n < k) :
    orderedKSubsetPairs n k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨A, B⟩ hAB
  rw [mem_orderedKSubsetPairs] at hAB
  have hle : A.card ≤ n := by
    simpa using card_le_card hAB.1
  rw [hAB.2.1] at hle
  exact (not_le_of_gt h) hle

/-- The ordered-pair count is zero when `n < k`. -/
theorem card_orderedKSubsetPairs_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    (orderedKSubsetPairs n k).card = 0 := by
  rw [orderedKSubsetPairs_eq_empty_of_lt h, card_empty]

/-- The ordered-pair count is bounded by the unfiltered product count. -/
theorem card_orderedKSubsetPairs_le_choose_mul_choose (n k : ℕ) :
    (orderedKSubsetPairs n k).card ≤ Nat.choose n k * Nat.choose n k := by
  unfold orderedKSubsetPairs
  calc
    ((((range n).powersetCard k).product ((range n).powersetCard k)).filter
          (fun AB => List.Forall₂ (· ≤ ·) (AB.1.sort (· ≤ ·))
            (AB.2.sort (· ≤ ·)))).card
        ≤ (((range n).powersetCard k).product ((range n).powersetCard k)).card :=
          card_filter_le _ _
    _ = Nat.choose n k * Nat.choose n k := by
      simp [card_product, card_powersetCard]

end Finset
