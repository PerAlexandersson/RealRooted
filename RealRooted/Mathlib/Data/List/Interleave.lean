/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Batteries.Data.List.Lemmas
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Unbundled

import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Simproc.ExistsAndEq
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Interleaving lists

This file defines interleaving of lists, both as an operation and as a relation.

The local `List.interleaveRight` starts with the right list and stops when that
list is empty. It deliberately differs from Batteries' `List.interleave`, which
starts with the left list and retains leftover entries. The distinction keeps
the existing `List.Interleaves` convention unchanged.
-/

public section

namespace List
variable {α : Type*} {r s : α → α → Prop} {l l₁ l₂ : List α} {a b c : α}

/-- Interleaves two lists `l₁` and `l₂`, starting with an element of `l₂`.
This operation is well-behaved only when the length of `l₂` is either the length of `l₁`
or one more.
```
#eval interleaveRight [1, 3] [0, 2, 4] -- [0, 1, 2, 3, 4]
#eval interleaveRight [0, 1, 2] [3, 4]
```
-/
@[expose]
def interleaveRight : List α → List α → List α
  | _, [] => []
  | l₁, a :: l₂ => a :: interleaveRight l₂ l₁
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp] lemma interleaveRight_nil (l₁ : List α) : l₁.interleaveRight [] = [] := by
  rw [interleaveRight]

@[simp]
lemma interleaveRight_cons (l₁ : List α) (a : α) (l₂ : List α) :
    l₁.interleaveRight (a :: l₂) = a :: interleaveRight l₂ l₁ := by rw [interleaveRight]

@[simp]
lemma interleaveRight_append_append_of_length_eq_length :
    ∀ {l₁ l₂ : List α} (_ : l₁.length = l₂.length) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleaveRight (l₂ ++ l₄) = l₁.interleaveRight l₂ ++ l₃.interleaveRight l₄
  | [], [], _, l₃, l₄ => by simp
  | a :: l₁, b :: l₂, _, l₃, l₄ => by
      simp_all [interleaveRight_append_append_of_length_eq_length]

@[simp]
lemma interleaveRight_append_left_of_length_eq_length
    (h₁₂ : l₁.length = l₂.length) (l₃ : List α) :
    (l₁ ++ l₃).interleaveRight l₂ = l₁.interleaveRight l₂ ++ l₃.interleaveRight [] := by
  simpa using interleaveRight_append_append_of_length_eq_length h₁₂ _ []

@[simp]
lemma interleaveRight_append_right_of_length_eq_length
    (h₁₂ : l₁.length = l₂.length) (l₃ : List α) :
    l₁.interleaveRight (l₂ ++ l₃) = l₁.interleaveRight l₂ ++ [].interleaveRight l₃ := by
  simpa using interleaveRight_append_append_of_length_eq_length h₁₂ [] _

@[simp]
lemma interleaveRight_append_append_of_length_add_one_eq_length :
    ∀ {l₁ l₂ : List α} (_ : l₁.length + 1 = l₂.length) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleaveRight (l₂ ++ l₄) = l₁.interleaveRight l₂ ++ l₄.interleaveRight l₃
  | [], b :: l₂, _, l₃, l₄ => by simp_all
  | a :: l₁, b :: c :: l₂, _, l₃, l₄ => by
      simp_all [interleaveRight_append_append_of_length_eq_length]

@[simp]
lemma interleaveRight_append_left_of_length_add_one_eq_length (h₁₂ : l₁.length + 1 = l₂.length)
    (l₃ : List α) :
    (l₁ ++ l₃).interleaveRight l₂ = l₁.interleaveRight l₂ ++ [].interleaveRight l₃ := by
  simpa using interleaveRight_append_append_of_length_add_one_eq_length h₁₂ _ []

@[simp]
lemma interleaveRight_append_right_of_length_add_one_eq_length (h₁₂ : l₁.length + 1 = l₂.length)
    (l₃ : List α) :
    l₁.interleaveRight (l₂ ++ l₃) = l₁.interleaveRight l₂ ++ l₃.interleaveRight [] := by
  simpa using interleaveRight_append_append_of_length_add_one_eq_length h₁₂ [] _

@[simp]
lemma reverse_interleaveRight_of_length_eq_length :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length →
      (l₁.interleaveRight l₂).reverse = l₂.reverse.interleaveRight l₁.reverse
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, _ => by simp_all [reverse_interleaveRight_of_length_eq_length]

@[simp]
lemma reverse_interleaveRight_of_length_add_one_eq_length :
    ∀ {l₁ l₂ : List α}, l₁.length + 1 = l₂.length →
      (l₁.interleaveRight l₂).reverse = l₁.reverse.interleaveRight l₂.reverse
  | [], [a], _ => by simp
  | a :: l₁, b :: l₂, _ => by simp_all [reverse_interleaveRight_of_length_add_one_eq_length]

@[simp]
lemma interleaveRight_ofFn_ofFn :
    ∀ {n : ℕ} {f g : Fin n → α},
      interleaveRight (ofFn f) (ofFn g) =
        ofFn (n := 2 * n) (fun i ↦
          if i.val % 2 = 0 then g ⟨i / 2, by lia⟩ else f ⟨i / 2, by lia⟩)
  | 0, f, g  => by simp
  | n + 1, f, g => by
      simp_all [interleaveRight_ofFn_ofFn]
      grind [Nat.add_div_right, Nat.add_mod_right, Nat.mul_add_div, Nat.mul_add_mod]

lemma interleaveRight_ofFn_ofFn' :
    ∀ {n : ℕ} {f : Fin n → α} {g : Fin (n + 1) → α},
      interleaveRight (ofFn f) (ofFn g) =
        ofFn (n := 2 * n + 1)
          (fun i ↦ if hi : i.val % 2 = 0 then g ⟨i / 2, by lia⟩ else f ⟨i / 2, by lia⟩)
  | 0, f, g  => by simp
  | n + 1, f, g => by
      simp_all only [ofFn_succ, Fin.succ_zero_eq_one, interleaveRight_cons,
        interleaveRight_ofFn_ofFn, Fin.succ_mk, Fin.val_zero, Nat.zero_mod, ↓reduceDIte,
        Nat.zero_div, Fin.zero_eta, Fin.val_succ, Nat.zero_add, Nat.mod_succ,
        Nat.succ_ne_self, Nat.reduceDiv, Nat.mul_eq, Nat.reduceAdd, Nat.mod_self,
        Nat.zero_lt_succ, Nat.div_self, Fin.mk_one, cons.injEq, true_and]
      congr 1
      funext i
      by_cases hc : (i : ℕ) % 2 = 0
      · rw [ite_eq_left hc, dite_eq_right (by lia : ¬ ((i : ℕ) + 3) % 2 = 0)]
        congr 1
        simp only [Fin.mk.injEq]
        lia
      · rw [ite_eq_right hc, dite_eq_left (by lia : ((i : ℕ) + 3) % 2 = 0)]
        congr 1
        simp only [Fin.mk.injEq]
        lia

@[simp]
lemma left_sublist_interleaveRight :
    ∀ {l₁ l₂ : List α}, l₁.length ≤ l₂.length → l₁ <+ l₁.interleaveRight l₂
  | [], _, _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [interleaveRight_cons]
    exact .cons _ <| .cons_cons _ <| left_sublist_interleaveRight <| by grind

@[simp]
lemma right_sublist_interleaveRight {l₁ l₂ : List α} (hl : l₂.length ≤ l₁.length + 1) :
    l₂ <+ l₁.interleaveRight l₂ := by cases l₂ <;> simp_all

variable (r) in
/-- Relation for interleaving lists. `l₁` `r`-interleaves `l₂` if the length
of `l₂` is either the length of `l₁` or one more and if the `i`-th rightmost
element of `l₁` is `r`-related to both the `i`-th and `i + 1`-st rightmost
elements of `l₂`, except possibly when `i = l₁.length`.

For example, `[1, 3]` `(· ≥ ·)`-interleaves `[0, 2, 4]`.

See `interleaves_iff_length_isChain_interleaveRight` for the connection with
`List.interleaveRight`. -/
@[mk_iff]
inductive Interleaves : List α → List α → Prop
  /-- The empty list interleaves itself. -/
  | nil_nil : Interleaves [] []
  /-- The empty list interleaves any singleton list. -/
  | nil_singleton (a : α) : Interleaves [] [a]
  /-- If `l₁` interleaves `b :: l₂` and `a` is related to `b`, then `b :: l₂` interleaves
  `a :: l₁`. -/
  | cons_symm ⦃l₁ l₂ : List α⦄ ⦃b : α⦄ (hl : Interleaves l₁ (b :: l₂))
      ⦃a : α⦄ (hab : r a b) :
      Interleaves (b :: l₂) (a :: l₁)

attribute [simp] Interleaves.nil_nil
attribute [simp high] Interleaves.nil_singleton

@[simp]
lemma interleaves_nil_cons : Interleaves r [] (a :: l) ↔ l = [] := by
  rw [interleaves_iff]
  simp

@[simp]
lemma not_interleaves_cons_nil : ¬ Interleaves r (a :: l) [] := by
  rw [interleaves_iff]
  simp

@[simp]
lemma interleaves_cons_cons :
    Interleaves r (a :: l₁) (b :: l₂) ↔ r b a ∧ Interleaves r l₂ (a :: l₁) := by
  rw [interleaves_iff]
  simp [and_comm]

@[simp high]
lemma interleaves_singleton_singleton : Interleaves r [a] [b] ↔ r b a := by simp

@[gcongr]
lemma Interleaves.mono (hrs : ∀ ⦃a b⦄, r a b → s a b) :
    ∀ l₁ l₂ : List α, Interleaves r l₁ l₂ → Interleaves s l₁ l₂
  | _, _, .nil_nil => .nil_nil
  | _, _, .nil_singleton a => .nil_singleton _
  | _, _, .cons_symm hl hab => .cons_symm (hl.mono hrs) <| hrs hab

/-- Mapping two interleaving lists along a relation-preserving function
preserves their interleaving. -/
lemma Interleaves.map
    {β : Type*} {s : β → β → Prop} {l₁ l₂ : List α}
    (h : Interleaves r l₁ l₂) (φ : α → β)
    (hφ : ∀ ⦃a b⦄, r a b → s (φ a) (φ b)) :
    Interleaves s (l₁.map φ) (l₂.map φ) := by
  induction h with
  | nil_nil => exact .nil_nil
  | nil_singleton a => exact .nil_singleton (φ a)
  | cons_symm h hab ih => exact .cons_symm ih (hφ hab)

/-- Mapping two interleaving lists along a relation-preserving function on
their entries preserves their interleaving. -/
lemma Interleaves.map_of_mem
    {β : Type*} {s : β → β → Prop} {l₁ l₂ : List α}
    (h : Interleaves r l₁ l₂) (φ : α → β)
    (hφ : ∀ ⦃a b⦄, (a ∈ l₁ ∨ a ∈ l₂) → (b ∈ l₁ ∨ b ∈ l₂) →
      r a b → s (φ a) (φ b)) :
    Interleaves s (l₁.map φ) (l₂.map φ) := by
  induction h with
  | nil_nil => simp
  | nil_singleton a => simp
  | cons_symm h hab ih =>
      rename_i l₁ l₂ b a
      simp only [map_cons]
      have hmid : Interleaves s (l₁.map φ) (φ b :: l₂.map φ) := by
        grind
      simp_all

lemma interleaves_iff_length_isChain_interleaveRight :
    ∀ {l₁ l₂ : List α},
    Interleaves r l₁ l₂ ↔
      (l₁.length = l₂.length ∨ l₁.length + 1 = l₂.length) ∧
        (l₁.interleaveRight l₂).IsChain r
  | [], [] => by simp
  | [], b :: l₂ => by simp
  | a :: l₁, [] => by simp
  | a :: l₁, [b] => by rw [interleaves_iff]; simp
  | a :: l₁, b :: l₂ => by
    rw [interleaves_iff]
    simp only [reduceCtorEq, and_self, cons.injEq, false_and, exists_false,
      ↓existsAndEq, true_and,
      exists_eq_right_right', false_or, length_cons, Nat.add_right_cancel_iff, interleaveRight_cons,
      isChain_cons_cons]
    rw [interleaves_iff_length_isChain_interleaveRight]
    simp [or_comm, eq_comm, and_comm, and_assoc]
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp]
lemma interleaves_append_singleton_append_singleton_of_length_eq_length
    (h : l₁.length = l₂.length) :
    Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r b a ∧ Interleaves r l₁ (l₂ ++ [b]) := by
  simp [interleaves_iff_length_isChain_interleaveRight, and_comm, *]

@[simp]
lemma interleaves_append_singleton_append_singleton_of_length_add_one_eq_length
    (h : l₁.length + 1 = l₂.length) :
    Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r a b ∧ Interleaves r (l₁ ++ [a]) l₂ := by
  simp [interleaves_iff_length_isChain_interleaveRight, and_comm, *]

lemma interleaves_reverse_reverse_of_length_eq_length (h : l₁.length = l₂.length) :
    Interleaves r l₁.reverse l₂.reverse ↔ Interleaves (Function.swap r) l₂ l₁ := by
  simp [interleaves_iff_length_isChain_interleaveRight,
    ← reverse_interleaveRight_of_length_eq_length,
    isChain_reverse, *]

lemma interleaves_reverse_reverse_of_length_add_one_eq_length (h : l₁.length + 1 = l₂.length) :
  Interleaves r l₁.reverse l₂.reverse ↔ Interleaves (Function.swap r) l₁ l₂ := by
  simp [interleaves_iff_length_isChain_interleaveRight,
    ← reverse_interleaveRight_of_length_add_one_eq_length,
    isChain_reverse, *]

lemma interleaves_ofFn {n : ℕ} {f g : Fin n → α} :
    Interleaves r (ofFn f) (ofFn g) ↔
      (∀ i, r (g i) (f i)) ∧
        ∀ (i : ℕ) (hi : i + 1 < n), r (f ⟨i, by lia⟩) (g ⟨i + 1, hi⟩) := by
  simp only [interleaves_iff_length_isChain_interleaveRight, length_ofFn,
    Nat.succ_ne_self, or_false,
    interleaveRight_ofFn_ofFn, isChain_ofFn, true_and]
  refine ⟨fun h ↦ ?_, fun h i hi ↦ by have := h.1 ⟨i / 2, by lia⟩; grind⟩
  exact ⟨fun i ↦ by have := h (2 * i); grind, fun i hi ↦ by have := h (2 * i + 1); grind⟩

lemma interleaves_ofFn' {n : ℕ} {f : Fin n → α} {g : Fin (n + 1) → α} :
    Interleaves r (ofFn f) (ofFn g) ↔
      (∀ i : Fin n, r (f i) (g i.succ)) ∧
        ∀ i : Fin n, r (g i.castSucc) (f i) := by
  simp only [interleaves_iff_length_isChain_interleaveRight, length_ofFn, Nat.left_eq_add,
    interleaveRight_ofFn_ofFn', isChain_ofFn, Nat.succ_ne_self, or_true, true_and]
  -- FIXME: Why doesn't `grind unfold these?
  unfold Fin.castSucc Fin.castAdd Fin.castLE
  refine ⟨fun h ↦ ?_, fun h i hi ↦ by
    grind⟩
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · have := h (2 * i + 1)
    grind
  · have := h (2 * i)
    grind

variable [IsTrans α r]

lemma Interleaves.pairwise_left (hl : Interleaves r l₁ l₂) : l₁.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleaveRight] at hl
  exact hl.2.pairwise.sublist <| left_sublist_interleaveRight <| by lia

lemma Interleaves.pairwise_right (hl : Interleaves r l₁ l₂) : l₂.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleaveRight] at hl
  exact hl.2.pairwise.sublist <| right_sublist_interleaveRight <| by lia

end List
