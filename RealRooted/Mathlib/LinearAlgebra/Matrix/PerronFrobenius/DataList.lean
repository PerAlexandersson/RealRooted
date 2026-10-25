/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Data.List.Basic

/-!
# Auxiliary list lemmas

Lemmas about `List.concat`, `List.dropLast`, `List.tail` and `List.idxOf` for lists without
duplicates, used for paths in quivers. They describe membership in `l.concat x` and in its tail,
and show that the last entry of a duplicate-free list does not occur in `l.dropLast` and has index
`l.length - 1`.

## Main statements

* `List.mem_concat`: `a ∈ l.concat x ↔ a ∈ l ∨ a = x`.
* `List.head_not_mem_tail_of_nodup`: the head of a duplicate-free list is not in its tail.
* `List.not_mem_dropLast_getLast`: the last entry of a duplicate-free list is not in
  `l.dropLast`.
* `List.idxOf_eq_length_sub_one_of_getLast`: if `x` is the last entry of `l` and `x ∉ l.dropLast`,
  then `l.idxOf x = l.length - 1`.
* `List.mem_tail_concat_of_ne_nil`: membership in the tail of `l.concat y` for nonempty `l`.

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.
Declarations that RealRooted does not use were removed (2026-10-07).
Original path: MCMC/PF/Data/List.lean
-/

@[expose] public section

namespace List
open List
variable {α : Type*}

/--
An element `a` is a member of `l.concat x` if and only if it is a member of `l` or is equal to `x`.
-/
theorem mem_concat {a x : α} {l : List α} : a ∈ l.concat x ↔ a ∈ l ∨ a = x := by
  rw [concat_eq_append,List.mem_append, List.mem_singleton, or_comm]

-- `dropLast_cons_cons` is now in Mathlib.

variable {α : Type*} {l m : List α} {n : ℕ}

variable {α : Type*} [DecidableEq α]

namespace Nat
@[deprecated Nat.eq_zero_of_le_zero (since := "2026-10-11")]
alias eq_of_le_zero := Nat.eq_zero_of_le_zero
end Nat

omit [DecidableEq α] in
/-- For a *non-empty* list the first element is not contained in the `tail`,
    provided the list has no duplicates. -/
lemma head_not_mem_tail_of_nodup {l : List α} (h : l.Nodup) (h_nonempty : l ≠ []) :
    l.head h_nonempty ∉ l.tail := by
  cases l with
  | nil => contradiction
  | cons hd tl =>
    simp only [nodup_cons] at h
    simp_all only [tail_cons, head_cons, not_false_eq_true]

@[simp] lemma idxOf_eq_length_sub_one_of_getLast
    {l : List α} {x : α}
    (h_nonempty : l ≠ [])
    (h_last : l.getLast h_nonempty = x)
    (h_unique : x ∉ l.dropLast) :
    l.idxOf x = l.length - 1 := by
  have hx : x ∈ l := by
    rw [← h_last]
    exact getLast_mem h_nonempty
  have h_idx_ge : l.length - 1 ≤ l.idxOf x := by
    by_contra h
    rw [not_le] at h
    have h_mem_dropLast : x ∈ l.dropLast := by
      rw [dropLast_eq_take]; rw [@mem_take_iff_getElem]
      use l.idxOf x
      constructor
      · exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hx)
      · subst h_last
        simp_all only [getLast_mem, tsub_le_iff_right, le_add_iff_nonneg_right, le_refl,
          Nat.eq_zero_of_le_zero, zero_le, inf_of_le_left]
    contradiction
  have h_idx_lt : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  exact Nat.le_antisymm (Nat.le_sub_one_of_lt h_idx_lt) h_idx_ge

attribute [simp] head_not_mem_tail_of_nodup

/-- Membership in the tail of `l.concat y`.
It is only useful if `l` is **non-empty** – we require `hl : l ≠ []`. -/
lemma mem_tail_concat_of_ne_nil
    {α : Type*} {l : List α} (hl : l ≠ []) (x y : α) :
    x ∈ (l.concat y).tail ↔ x ∈ l.tail ∨ x = y := by
  cases l with
  | nil      => exact (hl rfl).elim
  | cons _ t => simp only [concat_eq_append, cons_append, tail_cons, mem_append, mem_cons,
    not_mem_nil, or_false]

omit [DecidableEq α] in
@[simp]
lemma not_mem_dropLast_getLast {l : List α}
    (h₁ : l ≠ []) (h₂ : l.Nodup) :
    l.getLast h₁ ∉ l.dropLast := by
  induction l using List.reverseRecOn with
  | nil =>
      cases h₁ rfl
  | append_singleton xs x ih =>
      simp only [getLast_append_singleton] at *
      have h_disj : List.Disjoint xs [x] := disjoint_of_nodup_append h₂
      have hx_not_mem : x ∉ xs := (List.disjoint_singleton).1 h_disj
      simpa using hx_not_mem

end List
