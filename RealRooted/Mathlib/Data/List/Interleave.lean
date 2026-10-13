/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Batteries.Data.List.Interleave
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Nat.SuccPred

import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn

/-!
# Interleaving lists

This file defines interleaving of lists as a relation.

## See also

Interleaving of lists as an operation is defined in `Batteries/Data/List/Interleave.lean`.
-/

public section

namespace List
variable {α : Type*} {r s : α → α → Prop} {l l₁ l₂ l₃ l₄ : List α} {a b c : α}

private lemma nat_covBy_iff {m n : ℕ} : m ⋖ n ↔ m + 1 = n := by
  constructor
  · intro h
    simpa [Nat.succ_eq_add_one] using (Order.succ_eq_iff_covBy.mpr h)
  · intro h
    apply Order.succ_eq_iff_covBy.mp
    simpa [Nat.succ_eq_add_one] using h

private lemma nat_wcovBy_iff {m n : ℕ} : m ⩿ n ↔ m = n ∨ m + 1 = n := by
  rw [wcovBy_iff_eq_or_covBy, nat_covBy_iff]

variable (r) in
/-- Relation for interleaving lists. `l₁.Interleaves l₂ r` means that `l₁` `r`-interleaves `l₂`,
i.e. the length of `l₂` is either the length of `l₁` or one more and for each `i` the `i`-th
rightmost element of `l₁` is `r`-related to both the `i`-th and `i + 1`-st rightmost elements of
`l₂`, except possibly when `i = l₁.length`.

For example, `[1, 3]` `(· ≤ ·)`-interleaves both of `[0, 2, 4]` and `[0, 2]`.

See `interleaves_iff_length_isChain_interleave` for the connection with `List.interleave`. -/
@[mk_iff]
inductive Interleaves : List α → List α → Prop
  /-- The empty list interleaves itself. -/
  | nil_nil : Interleaves [] []
  /-- The empty list interleaves any singleton list. -/
  | nil_singleton (a : α) : Interleaves [] [a]
  /-- If `l₁` interleaves `b :: l₂` and `a` is related to `b`, then `b :: l₂` interleaves
  `a :: l₁`. -/
  | cons_symm ⦃a b : α⦄ (hab : r a b) ⦃l₁ l₂ : List α⦄ (hl : Interleaves l₁ (b :: l₂)) :
      Interleaves (b :: l₂) (a :: l₁)

attribute [simp] Interleaves.nil_nil
-- Should be higher priority than `interleaves_nil_cons`
attribute [simp high] Interleaves.nil_singleton

@[simp]
lemma interleaves_nil_cons : Interleaves r [] (a :: l) ↔ l = [] := by grind [interleaves_iff]

@[simp]
lemma not_interleaves_cons_nil : ¬ Interleaves r (a :: l) [] := by grind [interleaves_iff]

@[simp]
lemma interleaves_cons_cons :
    Interleaves r (a :: l₁) (b :: l₂) ↔ r b a ∧ Interleaves r l₂ (a :: l₁) := by
  grind [interleaves_iff]

-- Should be higher priority than `interleaves_cons_cons`
@[simp high]
lemma interleaves_singleton_singleton : Interleaves r [a] [b] ↔ r b a := by simp

@[gcongr]
lemma Interleaves.mono (hrs : ∀ ⦃a b⦄, r a b → s a b) :
    ∀ l₁ l₂ : List α, Interleaves r l₁ l₂ → Interleaves s l₁ l₂
  | _, _, .nil_nil => .nil_nil
  | _, _, .nil_singleton a => .nil_singleton _
  | _, _, .cons_symm hab hl => .cons_symm (hrs hab) <| hl.mono hrs

lemma interleaves_iff_length_isChain_interleave :
    ∀ {l₁ l₂ : List α}, Interleaves r l₁ l₂ ↔ l₁.length ⩿ l₂.length ∧ (l₂.interleave l₁).IsChain r
  | [], [] => by simp
  | [], b :: l₂ => by
    constructor
    · intro h
      cases h
      simp [nat_wcovBy_iff]
    · rintro ⟨hlen, _⟩
      rw [nat_wcovBy_iff] at hlen
      rcases hlen with hlen | hlen
      · simp only [length_nil, length_cons] at hlen
        lia
      · have hlen' : l₂.length = 0 := by
          simp only [length_nil, length_cons, Nat.zero_add] at hlen
          lia
        have hl₂ : l₂ = [] := eq_nil_of_length_eq_zero hlen'
        subst l₂
        exact .nil_singleton _
  | a :: l₁, [] => by
    constructor
    · intro h
      cases h
    · rintro ⟨hlen, _⟩
      rw [nat_wcovBy_iff] at hlen
      rcases hlen with hlen | hlen
      · simp only [length_nil, length_cons] at hlen
        lia
      · simp only [length_nil, length_cons] at hlen
        lia
  | a :: l₁, [b] => by
    rw [interleaves_cons_cons, interleaves_nil_cons]
    constructor
    · rintro ⟨hab, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [nat_wcovBy_iff]
        exact Or.inl rfl
      · simpa using hab
    · rintro ⟨hlen, hchain⟩
      rw [nat_wcovBy_iff] at hlen
      rcases hlen with hlen | hlen
      · simp only [length_cons, length_nil] at hlen
        have hl₁ : l₁ = [] := eq_nil_of_length_eq_zero (by lia)
        subst l₁
        exact ⟨by simpa using hchain, rfl⟩
      · simp only [length_cons, length_nil] at hlen
        lia
  | a :: l₁, b :: l₂ => by
    rw [interleaves_iff]
    simp [interleaves_iff_length_isChain_interleave (l₁ := l₂) (l₂ := a :: l₁), or_comm,
      eq_comm, and_comm, and_assoc, nat_wcovBy_iff]
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp]
lemma interleaves_append_singleton_append_singleton_of_length_eq_length
    (h : l₁.length = l₂.length) :
    Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r b a ∧ Interleaves r l₁ (l₂ ++ [b]) := by
  simp [interleaves_iff_length_isChain_interleave, and_comm, *]

@[simp]
lemma interleaves_append_singleton_append_singleton_of_length_eq_length_add_one
    (h : l₁.length + 1 = l₂.length) :
    Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r a b ∧ Interleaves r (l₁ ++ [a]) l₂ := by
  simp [interleaves_iff_length_isChain_interleave, and_comm, *]

lemma interleaves_reverse_reverse_of_length_eq_length (h : l₁.length = l₂.length) :
    Interleaves r l₁.reverse l₂.reverse ↔ Interleaves (Function.swap r) l₂ l₁ := by
  simp [interleaves_iff_length_isChain_interleave, ← reverse_interleave_of_length_eq_length,
    isChain_reverse, *]

lemma interleaves_reverse_reverse_of_length_eq_length_add_one (h : l₁.length + 1 = l₂.length) :
    Interleaves r l₁.reverse l₂.reverse ↔ Interleaves (Function.swap r) l₁ l₂ := by
  simp [interleaves_iff_length_isChain_interleave, ← reverse_interleave_of_length_eq_length_add_one,
    isChain_reverse, *]

lemma interleaves_ofFn_even {n : ℕ} {f g : Fin n → α} :
    Interleaves r (ofFn f) (ofFn g) ↔
      (∀ i, r (g i) (f i)) ∧ ∀ (i : ℕ) (hi : i + 1 < n), r (f ⟨i, by lia⟩) (g ⟨i + 1, hi⟩) := by
  simp only [interleaves_iff_length_isChain_interleave, length_ofFn, nat_wcovBy_iff,
    interleave_ofFn_ofFn_even, isChain_ofFn, true_or, true_and]
  refine ⟨fun h ↦ ?_, by grind⟩
  exact ⟨fun i ↦ by have := h (2 * i); grind, fun i hi ↦ by have := h (2 * i + 1); grind⟩

lemma interleaves_ofFn_odd {n : ℕ} {f : Fin n → α} {g : Fin (n + 1) → α} :
    Interleaves r (ofFn f) (ofFn g) ↔
      (∀ i : Fin n, r (f i) (g i.succ)) ∧ ∀ i : Fin n, r (g i.castSucc) (f i) := by
  simp only [interleaves_iff_length_isChain_interleave, length_ofFn, nat_wcovBy_iff,
    interleave_ofFn_ofFn_odd, or_true, true_and, isChain_ofFn]
  -- FIXME: Why doesn't `grind` unfold these?
  unfold Fin.castSucc Fin.castAdd Fin.castLE
  refine ⟨fun h ↦ ?_, fun h i hi ↦ by grind⟩
  exact ⟨fun i ↦ by have := h (2 * i + 1); grind, fun i ↦ by have := h (2 * i); grind⟩

section

variable [IsTrans α r]

lemma Interleaves.pairwise_left (hl : Interleaves r l₁ l₂) : l₁.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleave] at hl
  exact hl.2.pairwise.sublist right_sublist_interleave

lemma Interleaves.pairwise_right (hl : Interleaves r l₁ l₂) : l₂.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleave] at hl
  exact hl.2.pairwise.sublist left_sublist_interleave

end

section UpstreamCandidates

/-- Mapping two interleaving lists along a relation-preserving function preserves their
interleaving. -/
lemma Interleaves.map
    {β : Type*} {s : β → β → Prop} {l₁ l₂ : List α}
    (h : Interleaves r l₁ l₂) (φ : α → β)
    (hφ : ∀ ⦃a b⦄, r a b → s (φ a) (φ b)) :
    Interleaves s (l₁.map φ) (l₂.map φ) := by
  induction h with
  | nil_nil => exact .nil_nil
  | nil_singleton a => exact .nil_singleton (φ a)
  | cons_symm hab h ih => exact .cons_symm (hφ hab) ih

/-- Mapping two interleaving lists along a relation-preserving function on their entries preserves
their interleaving. -/
lemma Interleaves.map_of_mem
    {β : Type*} {s : β → β → Prop} {l₁ l₂ : List α}
    (h : Interleaves r l₁ l₂) (φ : α → β)
    (hφ : ∀ ⦃a b⦄, (a ∈ l₁ ∨ a ∈ l₂) → (b ∈ l₁ ∨ b ∈ l₂) →
      r a b → s (φ a) (φ b)) :
    Interleaves s (l₁.map φ) (l₂.map φ) := by
  induction h with
  | nil_nil => simp
  | nil_singleton a => simp
  | cons_symm hab h ih =>
      simp only [map_cons]
      refine .cons_symm (hφ (Or.inr (by simp)) (Or.inl (by simp)) hab) ?_
      apply ih
      intro x y hx hy hxy
      apply hφ
      · rcases hx with hx | hx
        · exact Or.inr (by simp [hx])
        · exact Or.inl (by simpa using hx)
      · rcases hy with hy | hy
        · exact Or.inr (by simp [hy])
        · exact Or.inl (by simpa using hy)
      · exact hxy

end UpstreamCandidates

section Deprecated

@[deprecated (since := "2026-10-13")]
alias interleaves_reverse_reverse_of_length_add_one_eq_length :=
  interleaves_reverse_reverse_of_length_eq_length_add_one

end Deprecated

end List
