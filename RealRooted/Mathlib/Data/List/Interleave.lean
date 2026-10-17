/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.List.Interleave

/-!
# Interleaving lists: additions

`List.Interleaves` and its basic API are in Mathlib (`Mathlib.Data.List.Interleave`,
mathlib4#39870).  This file keeps the lemmas that are not upstream yet, and a deprecated alias.
-/

public section

namespace List

variable {α : Type*} {r : α → α → Prop}

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

end List
