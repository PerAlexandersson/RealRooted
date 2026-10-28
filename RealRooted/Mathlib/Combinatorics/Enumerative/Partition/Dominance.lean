/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# Dominance order on partitions

This file defines the dominance order on partitions of a fixed natural
number.  The relation is expressed using the row lengths of the associated
Young diagrams, padded by zeros.
-/

@[expose] public section

open Finset

namespace Nat.Partition

/-- The `i`-th part of a partition in weakly decreasing order, padded by
zeros.  The index is zero-based. -/
def part {n : ℕ} (mu : n.Partition) (i : ℕ) : ℕ :=
  (YoungDiagram.ofPartition mu).rowLen i

/-- The sum of the first `k` parts of a partition. -/
def prefixSum {n : ℕ} (mu : n.Partition) (k : ℕ) : ℕ :=
  ∑ i ∈ range k, mu.part i

/-- Dominance order on partitions of the same natural number.  Thus
`mu ≤ lambda` means that every initial sum of `mu` is at most the
corresponding initial sum of `lambda`. -/
def DominanceLE {n : ℕ} (mu lambda : n.Partition) : Prop :=
  ∀ k, mu.prefixSum k ≤ lambda.prefixSum k

instance {n : ℕ} : LE (n.Partition) := ⟨DominanceLE⟩

theorem le_iff_prefixSum_le {n : ℕ} {mu lambda : n.Partition} :
    mu ≤ lambda ↔ ∀ k, mu.prefixSum k ≤ lambda.prefixSum k :=
  Iff.rfl

@[simp]
theorem prefixSum_zero {n : ℕ} (mu : n.Partition) : mu.prefixSum 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_succ {n : ℕ} (mu : n.Partition) (k : ℕ) :
    mu.prefixSum (k + 1) = mu.prefixSum k + mu.part k := by
  simp [prefixSum, sum_range_succ]

/-- A prefix sum is the sum of the corresponding initial segment of the
decreasingly sorted parts. -/
theorem prefixSum_eq_sum_take_sort_parts {n : ℕ}
    (mu : n.Partition) (k : ℕ) :
    mu.prefixSum k = ((mu.parts.sort (· ≥ ·)).take k).sum := by
  rw [← YoungDiagram.rowLens_ofPartition_eq_sort_parts]
  let Y := YoungDiagram.ofPartition mu
  change (∑ i ∈ range k, Y.rowLen i) = (Y.rowLens.take k).sum
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, ih]
      by_cases hk : k < Y.rowLens.length
      · rw [List.sum_take_succ _ _ hk]
        simp
      · have hle : Y.rowLens.length ≤ k := Nat.le_of_not_gt hk
        have hkrow : Y.rowLen k = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hpos
          have hcell : (k, 0) ∈ Y :=
            YoungDiagram.mem_iff_lt_rowLen.mpr hpos
          have hkheight : k < Y.colLen 0 :=
            YoungDiagram.mem_iff_lt_colLen.mp hcell
          exact hk (by simpa using hkheight)
        rw [List.take_of_length_le hle,
          List.take_of_length_le (hle.trans (Nat.le_succ k)), hkrow,
          add_zero]

/-- A prefix sum counts the cells in the corresponding initial rows of the
Young diagram. -/
theorem prefixSum_eq_card_filter_fst {n : ℕ} (mu : n.Partition) (k : ℕ) :
    mu.prefixSum k =
      #{c ∈ (YoungDiagram.ofPartition mu).cells | c.1 < k} := by
  let Y := YoungDiagram.ofPartition mu
  have hf : ∀ c ∈ Y.cells.filter fun c => c.1 < k,
      c.1 ∈ range k := by simp
  have hr : ∀ i ∈ range k,
      #{c ∈ Y.cells.filter fun c => c.1 < k | c.1 = i} = Y.rowLen i := by
    intro i hi
    rw [YoungDiagram.rowLen_eq_card]
    apply congrArg Finset.card
    ext c
    have hik : i < k := mem_range.mp hi
    simp only [YoungDiagram.row, mem_filter, YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨hc, _⟩, heq⟩
      exact ⟨hc, heq⟩
    · rintro ⟨hc, heq⟩
      exact ⟨⟨hc, heq.symm ▸ hik⟩, heq⟩
  rw [prefixSum, Finset.card_eq_sum_card_fiberwise hf]
  exact Finset.sum_congr rfl fun i hi => (hr i hi).symm

private theorem topRows_eq_rectangle_union_right (Y : YoungDiagram) (k : ℕ) :
    Y.cells.filter (fun c => c.1 < Y.colLen k) =
      (range (Y.colLen k) ×ˢ range k) ∪
        Y.cells.filter (fun c => k ≤ c.2) := by
  ext ⟨i, j⟩
  simp only [mem_filter, YoungDiagram.mem_cells, mem_union,
    mem_product, mem_range]
  constructor
  · rintro ⟨hcell, hi⟩
    by_cases hj : j < k
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr ⟨hcell, Nat.le_of_not_gt hj⟩
  · rintro (⟨hi, hj⟩ | ⟨hcell, hkj⟩)
    · have hik : (i, k) ∈ Y :=
        YoungDiagram.mem_iff_lt_colLen.mpr hi
      exact ⟨Y.up_left_mem le_rfl (Nat.le_of_lt hj) hik, hi⟩
    · have hik : (i, k) ∈ Y :=
        Y.up_left_mem le_rfl hkj hcell
      exact ⟨hcell, YoungDiagram.mem_iff_lt_colLen.mp hik⟩

private theorem disjoint_rectangle_right (Y : YoungDiagram) (k : ℕ) :
    Disjoint (range (Y.colLen k) ×ˢ range k)
      (Y.cells.filter fun c => k ≤ c.2) := by
  rw [Finset.disjoint_left]
  grind

private theorem topRows_subset_rectangle_union_right
    (Y : YoungDiagram) (r k : ℕ) :
    Y.cells.filter (fun c => c.1 < r) ⊆
      (range r ×ˢ range k) ∪
        Y.cells.filter (fun c => k ≤ c.2) := by
  rintro ⟨i, j⟩ hij
  simp only [mem_filter, YoungDiagram.mem_cells] at hij
  simp only [mem_union, mem_product, mem_range, mem_filter,
    YoungDiagram.mem_cells]
  by_cases hj : j < k <;> simp_all

/-- A conjugate prefix sum counts cells in the corresponding initial columns. -/
theorem prefixSum_conjugate_eq_card_filter_snd {n : ℕ}
    (mu : n.Partition) (k : ℕ) :
    mu.conjugate.prefixSum k =
      #{c ∈ (YoungDiagram.ofPartition mu).cells | c.2 < k} := by
  rw [prefixSum_eq_card_filter_fst]
  let Y := YoungDiagram.ofPartition mu
  have hconj : YoungDiagram.ofPartition mu.conjugate = Y.transpose := by
    simp [Nat.Partition.conjugate, Y]
  rw [hconj]
  let e : ℕ × ℕ ≃ ℕ × ℕ := Equiv.prodComm ℕ ℕ
  have hfilter : Y.transpose.cells.filter (fun c => c.1 < k) =
      e.finsetCongr (Y.cells.filter fun c => c.2 < k) := by
    ext ⟨i, j⟩
    simp [e, and_comm]
  rw [hfilter]
  simp [Y]

/-- A conjugate prefix sum is the sum of the original parts truncated at
the prefix length. -/
theorem conjugate_prefixSum_eq_sum_min_parts {n : ℕ}
    (mu : n.Partition) (k : ℕ) :
    mu.conjugate.prefixSum k = (mu.parts.map (min k)).sum := by
  rw [prefixSum_conjugate_eq_card_filter_snd]
  let Y := YoungDiagram.ofPartition mu
  have hf : ∀ c ∈ Y.cells.filter (fun c => c.2 < k),
      c.1 ∈ range (Y.colLen 0) := by
    rintro ⟨i, j⟩ hij
    simp only [mem_filter, YoungDiagram.mem_cells] at hij
    rw [mem_range, ← YoungDiagram.mem_iff_lt_colLen]
    exact Y.up_left_mem le_rfl (Nat.zero_le j) hij.1
  have hr : ∀ i ∈ range (Y.colLen 0),
      #{c ∈ Y.cells.filter (fun c => c.2 < k) | c.1 = i} =
        min k (Y.rowLen i) := by
    intro i _
    rw [min_comm]
    have heq : {c ∈ Y.cells.filter (fun c => c.2 < k) | c.1 = i} =
        {i} ×ˢ range (min (Y.rowLen i) k) := by
      ext ⟨a, b⟩
      simp only [mem_filter, YoungDiagram.mem_cells,
        YoungDiagram.mem_iff_lt_rowLen, mem_product,
        mem_singleton, mem_range]
      constructor
      · rintro ⟨⟨hab, hbk⟩, hai⟩
        subst a
        exact ⟨rfl, lt_min hab hbk⟩
      · rintro ⟨rfl, hb⟩
        exact ⟨⟨(lt_min_iff.mp hb).1, (lt_min_iff.mp hb).2⟩, rfl⟩
    rw [heq]
    simp
  rw [Finset.card_eq_sum_card_fiberwise hf]
  rw [Finset.sum_congr rfl hr]
  calc
    ∑ i ∈ range (Y.colLen 0), min k (Y.rowLen i) =
        (Y.rowLens.map (min k)).sum := by
      rw [YoungDiagram.rowLens, Finset.sum_eq_multiset_sum,
        Finset.range_val, Multiset.range, Multiset.map_coe,
        Multiset.sum_coe]
      simp only [List.map_map, Function.comp_def]
    _ = (mu.parts.map (min k)).sum := by
      rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts]
      rw [← Multiset.sum_coe, ← Multiset.map_coe,
        Multiset.sort_eq]

/-- A part of the conjugate counts original parts strictly larger than
its zero-based index. -/
theorem conjugate_part_eq_card_filter_gt {n : ℕ}
    (mu : n.Partition) (k : ℕ) :
    mu.conjugate.part k = (mu.parts.filter (k < ·)).card := by
  have hstep : (mu.parts.map (min (k + 1))).sum =
      (mu.parts.map (min k)).sum +
        (mu.parts.filter (k < ·)).card := by
    induction mu.parts using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons,
          Multiset.filter_cons]
        by_cases h : k < a
        · rw [ite_eq_left h, Multiset.card_add,
            Multiset.card_singleton, ih,
            min_eq_left (Nat.succ_le_iff.mpr h),
            min_eq_left (Nat.le_of_lt h)]
          lia
        · have hak : a ≤ k := Nat.le_of_not_gt h
          rw [ite_eq_right h, Multiset.card_add,
            Multiset.card_zero, zero_add, ih, min_eq_right hak,
            min_eq_right (hak.trans (Nat.le_succ k))]
          lia
  have hsucc := conjugate_prefixSum_eq_sum_min_parts mu (k + 1)
  have hk := conjugate_prefixSum_eq_sum_min_parts mu k
  rw [prefixSum_succ, hk] at hsucc
  lia

/-- Truncating and summing all zero-padded parts over sufficiently many
indices gives the corresponding sum over the multiset of parts. -/
theorem sum_min_part_fin_eq_sum_min_parts {n q : ℕ}
    (mu : n.Partition) (hmu : mu.parts.card ≤ q) (k : ℕ) :
    (∑ i : Fin q, min k (mu.part i)) =
      (mu.parts.map (min k)).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun i => min k (mu.part i)) q]
  let Y := YoungDiagram.ofPartition mu
  change (∑ i ∈ range q, min k (Y.rowLen i)) = _
  have hheight : Y.colLen 0 ≤ q := by
    simpa [Y, ← YoungDiagram.length_rowLens,
      YoungDiagram.rowLens_ofPartition_eq_sort_parts] using hmu
  have hsub : range (Y.colLen 0) ⊆ range q :=
    range_mono hheight
  calc
    ∑ i ∈ range q, min k (Y.rowLen i) =
        ∑ i ∈ range (Y.colLen 0), min k (Y.rowLen i) := by
      symm
      apply Finset.sum_subset hsub
      intro i _ hi
      have hle : Y.colLen 0 ≤ i := by
        simpa using hi
      have hirow : Y.rowLen i = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        have hcell : (i, 0) ∈ Y :=
          YoungDiagram.mem_iff_lt_rowLen.mpr hpos
        exact (Nat.not_lt_of_ge hle)
          (YoungDiagram.mem_iff_lt_colLen.mp hcell)
      simp [hirow]
    _ = (Y.rowLens.map (min k)).sum := by
      rw [YoungDiagram.rowLens, Finset.sum_eq_multiset_sum,
        Finset.range_val, Multiset.range, Multiset.map_coe,
        Multiset.sum_coe]
      simp only [List.map_map, Function.comp_def]
    _ = (mu.parts.map (min k)).sum := by
      rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts]
      rw [← Multiset.sum_coe, ← Multiset.map_coe,
        Multiset.sort_eq]

/-- Two partitions of `n` with the same prefix sums are equal. -/
theorem eq_of_forall_prefixSum_eq {n : ℕ}
    {mu lambda : n.Partition}
    (h : ∀ k, mu.prefixSum k = lambda.prefixSum k) : mu = lambda := by
  have hpart : ∀ i, mu.part i = lambda.part i := by
    intro i
    have hi := h i
    have his := h (i + 1)
    rw [prefixSum_succ, prefixSum_succ, hi] at his
    exact Nat.add_left_cancel his
  have hdiagram : YoungDiagram.ofPartition mu =
      YoungDiagram.ofPartition lambda := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
    change j < mu.part i ↔ j < lambda.part i
    rw [hpart i]
  apply YoungDiagram.equivPartition.symm.injective
  exact Subtype.ext hdiagram

instance {n : ℕ} : PartialOrder (n.Partition) where
  le_refl mu k := le_rfl
  le_trans _ _ _ hmu hla k := (hmu k).trans (hla k)
  le_antisymm mu lambda hmu hla :=
    eq_of_forall_prefixSum_eq fun k => Nat.le_antisymm (hmu k) (hla k)

private theorem conjugate_le_conjugate_of_le {n : ℕ}
    {mu lambda : n.Partition} (h : lambda ≤ mu) :
    mu.conjugate ≤ lambda.conjugate := by
    intro k
    rw [prefixSum_conjugate_eq_card_filter_snd,
      prefixSum_conjugate_eq_card_filter_snd]
    let M := YoungDiagram.ofPartition mu
    let L := YoungDiagram.ofPartition lambda
    let r := L.colLen k
    let rect := range r ×ˢ range k
    let rightM := M.cells.filter fun c => k ≤ c.2
    let rightL := L.cells.filter fun c => k ≤ c.2
    have htop : #(L.cells.filter fun c => c.1 < r) ≤
        #(M.cells.filter fun c => c.1 < r) := by
      rw [← prefixSum_eq_card_filter_fst,
        ← prefixSum_eq_card_filter_fst]
      exact h r
    have hLtop : #(L.cells.filter fun c => c.1 < r) = r * k + #rightL := by
      rw [topRows_eq_rectangle_union_right]
      rw [Finset.card_union_of_disjoint (disjoint_rectangle_right L k)]
      simp [rightL, r]
    have hMtop : #(M.cells.filter fun c => c.1 < r) ≤ r * k + #rightM := by
      calc
        _ ≤ #(rect ∪ rightM) := Finset.card_le_card
          (topRows_subset_rectangle_union_right M r k)
        _ ≤ #rect + #rightM := Finset.card_union_le rect rightM
        _ = r * k + #rightM := by simp [rect]
    have hright : #rightL ≤ #rightM := by
      lia
    have hMsplit := Finset.card_filter_add_card_filter_not
      (s := M.cells) (fun c => c.2 < k)
    have hLsplit := Finset.card_filter_add_card_filter_not
      (s := L.cells) (fun c => c.2 < k)
    simp only [Nat.not_lt] at hMsplit hLsplit
    have hcardM : #M.cells = n := YoungDiagram.card_ofPartition mu
    have hcardL : #L.cells = n := YoungDiagram.card_ofPartition lambda
    lia

/-- Conjugating both partitions reverses dominance. -/
theorem conjugate_le_conjugate_iff {n : ℕ} {mu lambda : n.Partition} :
    mu.conjugate ≤ lambda.conjugate ↔ lambda ≤ mu := by
  constructor
  · intro h
    simpa only [conjugate_conjugate] using
      conjugate_le_conjugate_of_le h
  · exact conjugate_le_conjugate_of_le

/-- Conjugating both partitions reverses strict dominance. -/
theorem conjugate_lt_conjugate_iff {n : ℕ} {mu lambda : n.Partition} :
    mu.conjugate < lambda.conjugate ↔ lambda < mu := by
  have hinj : Function.Injective (@conjugate n) := by
    intro a b h
    simpa only [conjugate_conjugate] using congrArg conjugate h
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne,
    conjugate_le_conjugate_iff]
  simp only [hinj.eq_iff, ne_eq, ne_comm]

/-- The finite set of partitions dominated by `lambda`. -/
noncomputable def dominanceDownset {n : ℕ}
    (lambda : n.Partition) : Finset n.Partition := by
  classical
  exact Finset.univ.filter fun mu => mu ≤ lambda

@[simp]
theorem mem_dominanceDownset {n : ℕ} {mu lambda : n.Partition} :
    mu ∈ dominanceDownset lambda ↔ mu ≤ lambda := by
  classical
  simp [dominanceDownset]

theorem mem_erase_dominanceDownset {n : ℕ}
    {mu lambda : n.Partition} :
    mu ∈ (dominanceDownset lambda).erase lambda ↔ mu < lambda := by
  classical
  simp [lt_iff_le_and_ne, and_comm]

end Nat.Partition
