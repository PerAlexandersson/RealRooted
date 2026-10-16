/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.GeneratingSeries
public import Mathlib.Tactic

/-!
# Weak alternating words and the first-maximum recurrence

Appendix A.1 of the zig-zag Eulerian proof. The auxiliary list
model proves the first-maximum recurrence. A direct finite bijection identifies
its count with the actual `Fin n → Fin k` weak up-down words used in the paper.
-/

@[expose] public noncomputable section

open Finset

namespace RealRooted.ZigzagEulerian.ListWordAux

/-- Orientation of the step leaving position `L` (`true` = weakly up). -/
def orient (up : Bool) (L : ℕ) : Bool := if Even L then up else !up

/-- The step relation. -/
def rel (up : Bool) (a b : ℕ) : Bool := if up then decide (a ≤ b) else decide (b ≤ a)

/-- Weak alternation, with first step weakly up (`up = true`) or weakly down. -/
def altB : Bool → List ℕ → Bool
  | _, [] => true
  | _, [_] => true
  | up, a :: b :: l => rel up a b && altB (!up) (b :: l)

/-- The empty word is weakly alternating in either orientation. -/
@[simp] lemma altB_nil (up : Bool) : altB up [] = true := rfl
/-- Every one-letter word is weakly alternating. -/
@[simp] lemma altB_single (up : Bool) (a : ℕ) : altB up [a] = true := rfl
/-- Weak alternation separates into the first comparison and the remaining word. -/
lemma altB_cons_cons (up : Bool) (a b : ℕ) (l : List ℕ) :
    altB up (a :: b :: l) = (rel up a b && altB (!up) (b :: l)) := rfl

/-- The initial step has the chosen orientation. -/
lemma orient_zero (up : Bool) : orient up 0 = up := by simp [orient]

/-- Advancing one position reverses the initial orientation. -/
lemma orient_succ (up : Bool) (L : ℕ) : orient up (L + 1) = orient (!up) L := by
  unfold orient
  by_cases h : Even L
  · simp [h, Nat.even_add_one]
  · simp [h, Nat.even_add_one]

/-- Split weak alternation at a shared boundary letter. -/
lemma altB_append_cons (pre : List ℕ) : ∀ (up : Bool) (m : ℕ) (suf : List ℕ),
    altB up (pre ++ m :: suf) =
      (altB up (pre ++ [m]) && altB (orient up pre.length) (m :: suf)) := by
  induction pre with
  | nil => intro up m suf; simp [orient_zero]
  | cons a pre ih =>
    intro up m suf
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons_append, altB_cons_cons, List.length_cons,
        List.length_nil, zero_add, orient_succ, orient_zero, altB_single, Bool.and_true]
    | cons b pre =>
      simp only [List.cons_append, altB_cons_cons] at ih ⊢
      rw [ih (!up) m suf, List.length_cons, List.length_cons, orient_succ (up := up),
        Bool.and_assoc]
      simp [orient_succ]

/-- Appending a strictly larger letter tests the final upward orientation. -/
lemma altB_snoc_of_lt {pre : List ℕ} (hne : pre ≠ []) {m : ℕ} (hlt : ∀ x ∈ pre, x < m)
    (up : Bool) : altB up (pre ++ [m]) = (altB up pre && orient up (pre.length - 1)) := by
  obtain ⟨pre', a, rfl⟩ := List.eq_nil_or_concat pre |>.resolve_left hne
  simp only [List.concat_eq_append] at hlt ⊢
  have ha : a < m := hlt a (by simp)
  rw [List.append_assoc, List.singleton_append, altB_append_cons, List.length_append,
    List.length_singleton, Nat.add_sub_cancel]
  congr 1
  simp only [altB_cons_cons, altB_single, Bool.and_true, rel]
  cases orient up pre'.length <;> simp [ha.le, not_le.mpr ha]

/-- A leading maximal letter satisfies the first downward comparison automatically. -/
lemma altB_false_cons_of_le {m : ℕ} {suf : List ℕ} (hle : ∀ x ∈ suf, x ≤ m) :
    altB false (m :: suf) = altB true suf := by
  cases suf with
  | nil => rfl
  | cons b s =>
    rw [altB_cons_cons]
    simp [rel, hle b (by simp)]

/-- An upward comparison from a maximal letter forces the next letter to equal it. -/
lemma altB_true_cons_of_le {m b : ℕ} {s : List ℕ} (hle : ∀ x ∈ b :: s, x ≤ m) :
    altB true (m :: b :: s) = (decide (b = m) && altB true s) := by
  rw [altB_cons_cons]
  have hb : b ≤ m := hle b (by simp)
  by_cases h : b = m
  · subst h
    simp only [rel, ite_true, le_refl, decide_true, Bool.true_and, Bool.not_true, decide_true]
    exact altB_false_cons_of_le (fun x hx => hle x (by simp [hx]))
  · simp [rel, h, show ¬ m ≤ b by lia]

/-! ### Complement symmetry -/

/-- Complementing every letter reverses the orientation of weak alternation. -/
lemma altB_map_compl (k : ℕ) : ∀ (l : List ℕ) (up : Bool), (∀ x ∈ l, x < k) →
    altB up (l.map (fun x => k - 1 - x)) = altB (!up) l := by
  intro l
  induction l with
  | nil => intro up _; rfl
  | cons a l ih =>
    intro up hl
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [List.map_cons, altB_cons_cons] at ih ⊢
      rw [ih (!up) (fun x hx => hl x (by simp_all))]
      have ha := hl a (by simp)
      have hb := hl b (by simp)
      congr 1
      cases up <;> simp [rel] <;> lia

/-! ### The sets of words -/

/-- Lists of length `n` with letters in `{0, …, k-1}`. -/
def wordsF : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | n + 1, k => (Finset.range k ×ˢ wordsF n k).image (fun p => p.1 :: p.2)

/-- Membership in `wordsF` means the prescribed length and alphabet bound. -/
lemma mem_wordsF {n k : ℕ} {l : List ℕ} :
    l ∈ wordsF n k ↔ l.length = n ∧ ∀ x ∈ l, x < k := by
  induction n generalizing l with
  | zero =>
    simp only [wordsF, Finset.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; simp
    · exact fun h => h.1
  | succ n ih =>
    simp only [wordsF, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨a, l', ⟨ha, hl'⟩, rfl⟩
      rw [ih] at hl'
      refine ⟨by simp [hl'.1], ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact hl'.2 x hx
    · intro ⟨hlen, hl⟩
      cases l with
      | nil => simp at hlen
      | cons a l' =>
      refine ⟨a, l', ⟨hl a (by simp),
        ih.mpr ⟨by simpa using hlen, fun x hx => hl x (by simp [hx])⟩⟩,
          rfl⟩

/-- Number of weakly alternating words of length `n` over `{0, …, k-1}`. -/
def wordCount (up : Bool) (n k : ℕ) : ℕ :=
  ((wordsF n k).filter (fun l => altB up l = true)).card

/-- Letter complementation equates the two initial-orientation counts. -/
lemma wordCount_compl (n k : ℕ) : wordCount false n k = wordCount true n k := by
  unfold wordCount
  apply Finset.card_nbij'
    (fun l => l.map (fun x => k - 1 - x)) (fun l => l.map (fun x => k - 1 - x))
  · intro l hl
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hl ⊢
    refine ⟨⟨by simp [hl.1.1], fun x hx => ?_⟩, ?_⟩
    · simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hl.1.2 y hy; lia
    · rw [altB_map_compl k l true hl.1.2]; simpa using hl.2
  · intro l hl
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hl ⊢
    refine ⟨⟨by simp [hl.1.1], fun x hx => ?_⟩, ?_⟩
    · simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hl.1.2 y hy; lia
    · rw [altB_map_compl k l false hl.1.2]; simpa using hl.2
  · intro l hl
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hl
    simp only [List.map_map]
    conv_rhs => rw [← List.map_id l]
    apply List.map_congr_left
    intro x hx; have := hl.1.2 x hx; simp; lia
  · intro l hl
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hl
    simp only [List.map_map]
    conv_rhs => rw [← List.map_id l]
    apply List.map_congr_left
    intro x hx; have := hl.1.2 x hx; simp; lia

/-! ### Splitting at the first maximal letter -/

/-- The empty word is the unique word of length zero. -/
lemma wordsF_zero (k : ℕ) : wordsF 0 k = {[]} := rfl

/-- There is one weakly alternating word of length zero. -/
lemma wordCount_zero (up : Bool) (k : ℕ) : wordCount up 0 k = 1 := by
  simp [wordCount, wordsF_zero, Finset.filter_singleton]

/-- Words avoiding the largest letter are counted over the smaller alphabet. -/
lemma card_filter_not_max (up : Bool) (n k : ℕ) :
    ((wordsF n (k + 1)).filter (fun l => altB up l = true ∧ k ∉ l)).card =
      wordCount up n k := by
  unfold wordCount
  congr 1
  ext l
  simp only [Finset.mem_filter, mem_wordsF]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨h1, fun x hx => ?_⟩, h3⟩
    have := h2 x hx
    have : x ≠ k := fun h => h4 (h ▸ hx)
    lia
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun x hx => by have := h2 x hx; lia⟩, h3, fun hk => by
      have := h2 k hk; lia⟩

/-- Split words containing the largest letter at its first occurrence. -/
lemma card_filter_max (P : List ℕ → Prop) [DecidablePred P] (n k : ℕ) :
    ((wordsF n (k + 1)).filter (fun l => P l ∧ k ∈ l)).card =
      ∑ p ∈ Finset.range n,
        ((wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1)).filter
          (fun x => P (x.1 ++ k :: x.2))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun l => l.idxOf k) (t := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.filter_filter]
    apply Finset.card_nbij' (fun l => (l.take p, l.drop (p + 1))) (fun x => x.1 ++ k :: x.2)
    · intro l hl
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF, Finset.mem_product] at hl ⊢
      obtain ⟨⟨hlen, hlt⟩, ⟨hP, hk⟩, hidx⟩ := hl
      have hplt : p < l.length := hidx ▸ List.idxOf_lt_length_of_mem hk
      have hdec : l = l.take p ++ k :: l.drop (p + 1) := by
        conv_lhs => rw [← List.take_append_drop p l]
        rw [List.drop_eq_getElem_cons hplt]
        congr 2
        have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hk)
        simp only [hidx] at this
        exact this
      refine ⟨⟨⟨by simp; lia, fun x hx => ?_⟩, ⟨by simp; lia, fun x hx => ?_⟩⟩, ?_⟩
      · have h1 := hlt x (List.mem_of_mem_take hx)
        have h2 : x ≠ k := by
          rintro rfl
          have := (List.mem_take_iff_idxOf_lt hk).mp hx
          lia
        lia
      · exact hlt x (List.mem_of_mem_drop hx)
      · rw [← hdec]; exact hP
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF, Finset.mem_product] at hx ⊢
      obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hP⟩ := hx
      have hp' := Finset.mem_range.mp hp
      have hkpre : k ∉ x.1 := fun h => by have := h2 k h; lia
      refine ⟨⟨by simp; lia, fun y hy => ?_⟩, ⟨hP, by simp⟩, ?_⟩
      · simp only [List.mem_append, List.mem_cons] at hy
        rcases hy with hy | rfl | hy
        · have := h2 y hy; lia
        · lia
        · exact h4 y hy
      · rw [List.idxOf_append_of_notMem hkpre, List.idxOf_cons_self, h1]; rfl
    · intro l hl
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hl
      obtain ⟨_, ⟨_, hk⟩, hidx⟩ := hl
      have hplt : p < l.length := hidx ▸ List.idxOf_lt_length_of_mem hk
      simp only
      conv_rhs => rw [← List.take_append_drop p l]
      rw [List.drop_eq_getElem_cons hplt]
      congr 2
      have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hk)
      simp only [hidx] at this
      exact this.symm
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF, Finset.mem_product] at hx
      obtain ⟨⟨⟨h1, _⟩, _⟩, _⟩ := hx
      simp only
      have e : x.1 ++ k :: x.2 = (x.1 ++ [k]) ++ x.2 := by simp
      refine Prod.ext (List.take_left' h1) ?_
      simp only
      rw [e, List.drop_left' (by simp [h1])]
  · intro l hl
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hl
    simp only [Finset.coe_range, Set.mem_Iio]
    rw [← hl.1.1]
    exact List.idxOf_lt_length_of_mem hl.2.2

/-- Reversing the initial orientation reverses every step orientation. -/
lemma orient_not (up : Bool) (L : ℕ) : orient (!up) L = !orient up L := by
  unfold orient; split_ifs <;> simp

/-- The terms of the split with a nonempty prefix. -/
lemma term_pos (up : Bool) (n k p : ℕ) (hp : 1 ≤ p) :
    ((wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1)).filter
        (fun x => altB up (x.1 ++ k :: x.2) = true)).card =
      if orient up (p - 1) = true then
        wordCount up p k * wordCount true (n - 1 - p) (k + 1) else 0 := by
  have key : ∀ x ∈ wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1),
      altB up (x.1 ++ k :: x.2) =
        (altB up x.1 && orient up (p - 1) && altB (!orient up (p - 1)) (k :: x.2)) := by
    intro x hx
    simp only [Finset.mem_product, mem_wordsF] at hx
    obtain ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩ := hx
    have hne : x.1 ≠ [] := by intro h; rw [h] at h1; simp at h1; lia
    rw [altB_append_cons, altB_snoc_of_lt hne h2, h1]
    have : orient up p = !orient up (p - 1) := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by lia⟩
      rw [orient_succ, orient_not, Nat.add_sub_cancel]
    rw [this]
  split_ifs with ho
  · rw [Finset.filter_congr (q := fun x => altB up x.1 = true ∧ altB true x.2 = true)]
    · rw [Finset.filter_product (p := fun l => altB up l = true)
        (q := fun l => altB true l = true), Finset.card_product]; rfl
    · intro x hx
      rw [key x hx, ho]
      simp only [Finset.mem_product, mem_wordsF] at hx
      rw [Bool.not_true, altB_false_cons_of_le (fun y hy => by have := hx.2.2 y hy; lia)]
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rw [key x hx]
    simp [ho]

/-- An empty prefix reduces a split-word count to its suffix count. -/
lemma card_single_product_filter (k m : ℕ) (Q : List ℕ → Prop) [DecidablePred Q] :
    ((wordsF 0 k ×ˢ wordsF m (k + 1)).filter (fun x => Q (x.1 ++ k :: x.2))).card =
      ((wordsF m (k + 1)).filter (fun s => Q (k :: s))).card := by
  rw [wordsF_zero, Finset.singleton_product, Finset.filter_map, Finset.card_map]
  rfl

/-- A first maximal letter contributes the upward suffix count in downward orientation. -/
lemma term_zero_false (n k : ℕ) :
    ((wordsF 0 k ×ˢ wordsF (n - 1 - 0) (k + 1)).filter
        (fun x => altB false (x.1 ++ k :: x.2) = true)).card = wordCount true (n - 1) (k + 1) := by
  rw [card_single_product_filter k _ (fun l => altB false l = true), Nat.sub_zero]
  unfold wordCount
  congr 1
  apply Finset.filter_congr
  intro s hs
  rw [mem_wordsF] at hs
  rw [altB_false_cons_of_le (fun y hy => by have := hs.2 y hy; lia)]

/-- An upward word starting at the maximum is empty or repeats that maximum. -/
lemma card_true_cons_max (k m : ℕ) :
    ((wordsF m (k + 1)).filter (fun s => altB true (k :: s) = true)).card =
      if m = 0 then 1 else wordCount true (m - 1) (k + 1) := by
  rcases m with _ | m
  · simp [wordsF_zero, Finset.filter_singleton]
  · rw [ite_eq_right (by lia), Nat.add_sub_cancel]
    unfold wordCount
    apply Finset.card_nbij' (fun s => s.tail) (fun s => k :: s)
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hs ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      cases s with
      | nil => simp at h1
      | cons b t =>
        rw [altB_true_cons_of_le (fun y hy => by have := h2 y hy; lia)] at h3
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
        exact ⟨⟨by simpa using h1, fun y hy => h2 y (by simp at hy; simp [hy])⟩, h3.2⟩
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hs ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      refine ⟨⟨by simp [h1], fun y hy => ?_⟩, ?_⟩
      · simp only [List.mem_cons] at hy; rcases hy with rfl | hy
        · lia
        · exact h2 y hy
      · rw [altB_true_cons_of_le (fun y hy => by
          simp only [List.mem_cons] at hy; rcases hy with rfl | hy
          · exact le_rfl
          · have := h2 y hy; lia)]
        simp [h3]
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_wordsF] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      cases s with
      | nil => simp at h1
      | cons b t =>
        rw [altB_true_cons_of_le (fun y hy => by have := h2 y hy; lia)] at h3
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
        simp [h3.1]
    · intro s _; rfl

/-- Partition the count by absence or first occurrence of the new maximal letter. -/
lemma wordCount_succ_split (up : Bool) (n k : ℕ) :
    wordCount up n (k + 1) = wordCount up n k + ∑ p ∈ Finset.range n,
      ((wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1)).filter
        (fun x => altB up (x.1 ++ k :: x.2) = true)).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (wordsF n (k + 1)).filter (fun l => altB up l = true)) (fun l => k ∈ l)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  rw [← card_filter_not_max up n k, ← card_filter_max (fun l => altB up l = true) n k,
    wordCount,
    ← h, add_comm]

/-- The recurrence (A.1) for weak up-down words. -/
theorem wordCount_rec (n k : ℕ) :
    2 * wordCount true n (k + 1) = 2 * wordCount true n k +
      ∑ p ∈ Finset.range n, wordCount true p k * wordCount true (n - 1 - p) (k + 1) +
      (if n = 1 then 1 else 0) + (if 2 ≤ n then wordCount true (n - 2) (k + 1) else 0) := by
  have hT := wordCount_succ_split true n k
  have hF := wordCount_succ_split false n k
  rw [wordCount_compl, wordCount_compl] at hF
  have hterm : ∀ p ∈ Finset.range n,
      ((wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1)).filter
        (fun x => altB true (x.1 ++ k :: x.2) = true)).card +
      ((wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1)).filter
        (fun x => altB false (x.1 ++ k :: x.2) = true)).card =
      wordCount true p k * wordCount true (n - 1 - p) (k + 1) +
        (if p = 0 then (if n - 1 = 0 then 1 else wordCount true (n - 1 - 1) (k + 1)) else 0) := by
    intro p _
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [card_single_product_filter k _ (fun l => altB true l = true), term_zero_false,
        Nat.sub_zero, card_true_cons_max, wordCount_zero]
      simp only [ite_true, one_mul]
      ring
    · have ho := orient_not true (p - 1)
      simp only [Bool.not_true] at ho
      rw [term_pos true n k p hp, term_pos false n k p hp, ho, wordCount_compl,
        ite_eq_right (show p ≠ 0 by lia)]
      cases orient true (p - 1) <;> simp
  have hsum := Finset.sum_add_distrib (s := Finset.range n)
    (f := fun p => ((wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1)).filter
        (fun x => altB true (x.1 ++ k :: x.2) = true)).card)
    (g := fun p => ((wordsF p k ×ˢ wordsF (n - 1 - p) (k + 1)).filter
        (fun x => altB false (x.1 ++ k :: x.2) = true)).card)
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
  have hlast : (if 0 ∈ Finset.range n then
      (if n - 1 = 0 then 1 else wordCount true (n - 1 - 1) (k + 1)) else 0) =
      (if n = 1 then 1 else 0) + (if 2 ≤ n then wordCount true (n - 2) (k + 1) else 0) := by
    rcases n with _ | _ | n
    · simp
    · simp
    · simp only [Finset.mem_range, show 0 < n + 1 + 1 by lia, ite_true,
        show n + 1 + 1 - 1 ≠ 0 by lia, ite_false, show n + 1 + 1 ≠ 1 by lia,
        show 2 ≤ n + 1 + 1 by lia, zero_add]
      rfl
  rw [hlast] at hsum
  lia

/-- A nonempty word cannot use the empty alphabet. -/
lemma wordCount_zero_letters (n : ℕ) (hn : 1 ≤ n) : wordCount true n 0 = 0 := by
  unfold wordCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl
  rw [mem_wordsF] at hl
  cases l with
  | nil => simp at hl; lia
  | cons a l => exact absurd (hl.2 a (by simp)) (by lia)

end RealRooted.ZigzagEulerian.ListWordAux

namespace RealRooted.ZigzagEulerian

private theorem altB_iff_fin : ∀ (l : List ℕ) (up : Bool),
    ListWordAux.altB up l = true ↔
      ∀ (i : ℕ) (h : i + 1 < l.length),
        ListWordAux.rel (ListWordAux.orient up i)
          (getElem l i (by lia)) (getElem l (i + 1) h) = true := by
  intro l
  induction l with
  | nil => intro up; simp
  | cons a l ih =>
    intro up
    cases l with
    | nil => simp
    | cons b l =>
      rw [ListWordAux.altB_cons_cons, Bool.and_eq_true, ih (!up)]
      constructor
      · rintro ⟨h0, h1⟩ i hi
        rcases i with _ | i
        · simpa [ListWordAux.orient_zero] using h0
        · have := h1 i (by simp at hi ⊢; lia)
          simpa [ListWordAux.orient_succ] using this
      · intro h
        refine ⟨by simpa [ListWordAux.orient_zero] using h 0 (by simp), fun i hi => ?_⟩
        have := h (i + 1) (by simp at hi ⊢; lia)
        simpa [ListWordAux.orient_succ] using this

private theorem rel_orient_true (i a b : ℕ) :
    ListWordAux.rel (ListWordAux.orient true i) a b = true ↔
      (Even i → a ≤ b) ∧ (Odd i → b ≤ a) := by
  unfold ListWordAux.orient ListWordAux.rel
  by_cases h : Even i
  · simp [h, Nat.not_odd_iff_even.mpr h]
  · simp [h, Nat.not_even_iff_odd.mp h]

/-- The list count is exactly the existing finite-function word count. -/
theorem weakUpDownWordCount_eq_listWordCount (n k : ℕ) :
    weakUpDownWordCount n k = ListWordAux.wordCount true n k := by
  classical
  unfold weakUpDownWordCount ListWordAux.wordCount
  apply Finset.card_bij (fun w _ => List.ofFn fun i => (w i).val)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, ListWordAux.mem_wordsF]
    refine ⟨?_, ?_⟩
    · refine ⟨List.length_ofFn, fun x hx => ?_⟩
      simp only [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact (w i).isLt
    · rw [altB_iff_fin]
      intro i hi
      have hi' : i + 1 < n := by simpa only [List.length_ofFn] using hi
      have hweak := hw ⟨i, by lia⟩ ⟨i + 1, hi'⟩ rfl
      by_cases he : Even i
      · have hweak' := hweak
        simp only [he, ite_true] at hweak'
        simpa [ListWordAux.rel, ListWordAux.orient, he] using hweak'
      · have hweak' := hweak
        simp only [he, ite_false] at hweak'
        simpa [ListWordAux.rel, ListWordAux.orient, he] using hweak'
  · intro w hw w' hw' h
    have h := List.ofFn_injective h
    funext i
    exact Fin.ext (congrFun h i)
  · intro l hl
    simp only [Finset.mem_filter, ListWordAux.mem_wordsF] at hl
    obtain ⟨⟨hlen, hlt⟩, halt⟩ := hl
    refine ⟨fun i => ⟨getElem l i.val (by lia), hlt _ (List.getElem_mem _)⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i j hij
      have hi : i.val + 1 < n := by lia
      have hiL : i.val + 1 < l.length := by lia
      have hrel := (altB_iff_fin l true).mp halt i.val hiL
      rw [rel_orient_true] at hrel
      have hidx : j.val = i.val + 1 := hij.symm
      have hj : j = ⟨i.val + 1, hi⟩ := Fin.ext hidx
      subst j
      by_cases he : Even i.val
      · simp only [he, ↓reduceIte]
        exact Fin.le_def.mpr (hrel.1 he)
      · simp only [he, ↓reduceIte]
        exact Fin.le_def.mpr (hrel.2 (Nat.not_even_iff_odd.mp he))
    · apply List.ext_getElem (by simp [hlen])
      intro i h1 h2
      simp

/-- First-maximum recurrence (A.1), stated for the actual weak up-down word count. -/
theorem weakUpDownWordCount_recurrence (n k : ℕ) :
    2 * weakUpDownWordCount n (k + 1) =
      2 * weakUpDownWordCount n k +
        ∑ p ∈ Finset.range n,
          weakUpDownWordCount p k * weakUpDownWordCount (n - 1 - p) (k + 1) +
        (if n = 1 then 1 else 0) +
        (if 2 ≤ n then weakUpDownWordCount (n - 2) (k + 1) else 0) := by
  simpa only [weakUpDownWordCount_eq_listWordCount] using
    ListWordAux.wordCount_rec n k

end RealRooted.ZigzagEulerian
