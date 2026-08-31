/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import RealRooted.Mathlib.Data.List.Interleave

/-!
# End padding for interleaving lists

This file records endpoint deletion and repeated endpoint padding for
`List.Interleaves`.  The statements are relation-generic, so applications to
ordered root lists do not need to reconstruct an `IsChain` proof.
-/

namespace List

variable {α : Type*} {r : α → α → Prop} {l₁ l₂ : List α} {a : α}

private lemma mem_interleave : ∀ (l₁ l₂ : List α) {x : α},
    x ∈ l₁.interleave l₂ → x ∈ l₁ ∨ x ∈ l₂
  | _, [], _, h => by
    simp at h
  | l₁, a :: l₂, x, h => by
    rw [interleave, mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr (by simp)
    · rcases mem_interleave l₂ l₁ h with h | h
      · exact Or.inr (mem_cons_of_mem _ h)
      · exact Or.inl h
  termination_by l₁ l₂ => l₁.length + l₂.length

private lemma nil_interleave_singleton (a : α) : ([] : List α).interleave [a] = [a] := by
  rw [interleave_cons, interleave_nil]

/-- Removing a final right-hand entry preserves an interleaving when the two
remaining lists have equal length. -/
lemma Interleaves.drop_right_of_length_eq
    (hlen : l₁.length = l₂.length) (h : Interleaves r l₁ (l₂ ++ [a])) :
    Interleaves r l₁ l₂ := by
  rw [interleaves_iff_length_isChain_interleave] at h ⊢
  obtain ⟨_, hchain⟩ := h
  refine ⟨Or.inl hlen, ?_⟩
  rw [interleave_append_right_of_length_eq_length hlen] at hchain
  exact (isChain_append.mp hchain).1

/-- Removing a final left-hand entry preserves an interleaving when the right
list is one entry longer. -/
lemma Interleaves.drop_left_of_length_add_one_eq
    (hlen : l₁.length + 1 = l₂.length) (h : Interleaves r (l₁ ++ [a]) l₂) :
    Interleaves r l₁ l₂ := by
  rw [interleaves_iff_length_isChain_interleave] at h ⊢
  obtain ⟨_, hchain⟩ := h
  refine ⟨Or.inr hlen, ?_⟩
  rw [interleave_append_left_of_length_add_one_eq_length hlen] at hchain
  exact (isChain_append.mp hchain).1

/-- Appending an upper endpoint to the right-hand list preserves an
interleaving of two equally long lists. -/
lemma Interleaves.append_right_of_length_eq
    (hlen : l₁.length = l₂.length) (h : Interleaves r l₁ l₂)
    (hupper : ∀ ⦃x⦄, x ∈ l₁ ∨ x ∈ l₂ → r x a) :
    Interleaves r l₁ (l₂ ++ [a]) := by
  rw [interleaves_iff_length_isChain_interleave] at h ⊢
  obtain ⟨_, hchain⟩ := h
  refine ⟨Or.inr (by simp [hlen]), ?_⟩
  rw [interleave_append_right_of_length_eq_length hlen]
  rw [nil_interleave_singleton]
  rw [isChain_append]
  refine ⟨hchain, ?_, ?_⟩
  · exact IsChain.singleton _
  intro x hx y hy
  simp only [head?_cons, Option.mem_some_iff] at hy
  subst y
  have hxmem : x ∈ l₁.interleave l₂ := mem_of_mem_getLast? hx
  exact hupper (mem_interleave _ _ hxmem)

/-- Appending an upper endpoint to the left-hand list preserves an
interleaving when the right-hand list is one entry longer. -/
lemma Interleaves.append_left_of_length_add_one_eq
    (hlen : l₁.length + 1 = l₂.length) (h : Interleaves r l₁ l₂)
    (hupper : ∀ ⦃x⦄, x ∈ l₁ ∨ x ∈ l₂ → r x a) :
    Interleaves r (l₁ ++ [a]) l₂ := by
  rw [interleaves_iff_length_isChain_interleave] at h ⊢
  obtain ⟨_, hchain⟩ := h
  refine ⟨Or.inl (by simp [hlen]), ?_⟩
  rw [interleave_append_left_of_length_add_one_eq_length hlen]
  rw [nil_interleave_singleton]
  rw [isChain_append]
  refine ⟨hchain, ?_, ?_⟩
  · exact IsChain.singleton _
  intro x hx y hy
  simp only [head?_cons, Option.mem_some_iff] at hy
  subst y
  have hxmem : x ∈ l₁.interleave l₂ := mem_of_mem_getLast? hx
  exact hupper (mem_interleave _ _ hxmem)

/-- Equal end padding preserves an interleaving of equally long lists; one
additional right-hand endpoint also preserves it. -/
lemma Interleaves.append_replicate_right_of_length_eq
    (hlen : l₁.length = l₂.length) (h : Interleaves r l₁ l₂)
    (hself : r a a) (hupper : ∀ ⦃x⦄, x ∈ l₁ ∨ x ∈ l₂ → r x a) :
    ∀ k : ℕ,
      Interleaves r (l₁ ++ List.replicate k a) (l₂ ++ List.replicate k a) ∧
      Interleaves r (l₁ ++ List.replicate k a) (l₂ ++ List.replicate (k + 1) a) := by
  intro k
  induction k with
  | zero =>
      simpa using ⟨h, h.append_right_of_length_eq hlen hupper⟩
  | succ k ih =>
      obtain ⟨ihsame, ihright⟩ := ih
      have hlenk : (l₁ ++ List.replicate k a).length =
          (l₂ ++ List.replicate k a).length := by
        simp only [length_append, length_replicate]
        lia
      have hsame : Interleaves r (l₁ ++ List.replicate (k + 1) a)
          (l₂ ++ List.replicate (k + 1) a) := by
        rw [show l₁ ++ List.replicate (k + 1) a =
              (l₁ ++ List.replicate k a) ++ [a] by
            rw [append_assoc, ← replicate_succ'],
          show l₂ ++ List.replicate (k + 1) a =
              (l₂ ++ List.replicate k a) ++ [a] by
            rw [append_assoc, ← replicate_succ']]
        rw [interleaves_append_singleton_append_singleton_of_length_eq_length hlenk]
        simpa [show l₂ ++ List.replicate k a ++ [a] =
              l₂ ++ List.replicate (k + 1) a by rw [append_assoc, ← replicate_succ']]
          using ⟨hself, ihright⟩
      refine ⟨hsame, ?_⟩
      have hupperk : ∀ ⦃x⦄, x ∈ l₁ ++ List.replicate (k + 1) a ∨
          x ∈ l₂ ++ List.replicate (k + 1) a → r x a := by
        intro x hx
        grind
      have hlenksucc : (l₁ ++ List.replicate (k + 1) a).length =
          (l₂ ++ List.replicate (k + 1) a).length := by
        simp only [length_append, length_replicate]
        lia
      simpa [Nat.add_assoc, append_assoc, replicate_succ'] using
        hsame.append_right_of_length_eq hlenksucc hupperk

/-- Equal end padding preserves an interleaving when the right-hand list is
one entry longer; one additional left-hand endpoint also preserves it. -/
lemma Interleaves.append_replicate_left_of_length_add_one_eq
    (hlen : l₁.length + 1 = l₂.length) (h : Interleaves r l₁ l₂)
    (hself : r a a) (hupper : ∀ ⦃x⦄, x ∈ l₁ ∨ x ∈ l₂ → r x a) :
    ∀ k : ℕ,
      Interleaves r (l₁ ++ List.replicate k a) (l₂ ++ List.replicate k a) ∧
      Interleaves r (l₁ ++ List.replicate (k + 1) a) (l₂ ++ List.replicate k a) := by
  intro k
  induction k with
  | zero =>
      simpa using ⟨h, h.append_left_of_length_add_one_eq hlen hupper⟩
  | succ k ih =>
      obtain ⟨ihsame, ihleft⟩ := ih
      have hlenk : (l₁ ++ List.replicate k a).length + 1 =
          (l₂ ++ List.replicate k a).length := by
        simp only [length_append, length_replicate]
        lia
      have hsame : Interleaves r (l₁ ++ List.replicate (k + 1) a)
          (l₂ ++ List.replicate (k + 1) a) := by
        rw [show l₁ ++ List.replicate (k + 1) a =
              (l₁ ++ List.replicate k a) ++ [a] by
            rw [append_assoc, ← replicate_succ'],
          show l₂ ++ List.replicate (k + 1) a =
              (l₂ ++ List.replicate k a) ++ [a] by
            rw [append_assoc, ← replicate_succ']]
        rw [interleaves_append_singleton_append_singleton_of_length_add_one_eq_length hlenk]
        simpa [show l₁ ++ List.replicate k a ++ [a] =
              l₁ ++ List.replicate (k + 1) a by rw [append_assoc, ← replicate_succ']]
          using ⟨hself, ihleft⟩
      refine ⟨hsame, ?_⟩
      have hupperk : ∀ ⦃x⦄, x ∈ l₁ ++ List.replicate (k + 1) a ∨
          x ∈ l₂ ++ List.replicate (k + 1) a → r x a := by
        intro x hx
        grind
      have hlenksucc : (l₁ ++ List.replicate (k + 1) a).length + 1 =
          (l₂ ++ List.replicate (k + 1) a).length := by
        simp only [length_append, length_replicate]
        lia
      simpa [Nat.add_assoc, append_assoc, replicate_succ'] using
        hsame.append_left_of_length_add_one_eq hlenksucc hupperk

end List
