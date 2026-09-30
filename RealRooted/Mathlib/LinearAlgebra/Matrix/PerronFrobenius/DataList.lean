/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina

Ported into RealRooted from https://github.com/or4nge19/MCMC
(commit dba8102fe7a333cb11966484e324d11e375f6624, Apache-2.0), with
adaptations to the pinned Mathlib.  Original path: MCMC/PF/Data/List.lean
-/
import Mathlib.Tactic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.List.Basic

-- Ported third-party code; keep original line layout.
set_option linter.style.longLine false
namespace List
open List
variable {α : Type*}

/--
A list `l` is disjoint from a singleton list `[x]` if and only if
`x` is not an element of `l`.
-/
@[simp]
lemma disjoint_singleton_right {l : List α} {x : α} :
  List.Disjoint l [x] ↔ x ∉ l :=
  List.disjoint_singleton

/--
An element `a` is a member of `l.concat x` if and only if it is a member of `l` or is equal to `x`.
-/
@[simp]
theorem mem_concat {a x : α} {l : List α} : a ∈ l.concat x ↔ a ∈ l ∨ a = x := by
  rw [concat_eq_append,List.mem_append, List.mem_singleton, or_comm]

/-- Any `x ∈ l` gives a decomposition `l = l₁ ++ x :: l₂`. -/
lemma exists_mem_split {l : List α} {x : α} (h : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  induction l with
  | nil     => cases h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h'
    · -- head
      exact ⟨[], ys, by simp only [List.nil_append]⟩
    · rcases ih h' with ⟨l₁, l₂, rfl⟩
      use y :: l₁, l₂
      simp only [List.cons_append]

-- `dropLast_cons_cons` is now in Mathlib.

variable {α : Type*} {l m : List α} {n : ℕ}

variable {α : Type*} [DecidableEq α]

/-- A list contains a duplicate element if the count of some element is greater than 1. -/
def ContainsDup {α : Type*} [DecidableEq α] (l : List α) : Prop :=
  ∃ x, 2 ≤ l.count x

lemma nodup_iff_not_contains_dup {α : Type*} [DecidableEq α] {l : List α} :
    l.Nodup ↔ ¬l.ContainsDup := by
  rw [List.nodup_iff_count_le_one, List.ContainsDup, not_exists]
  constructor
  · intro h x
    specialize h x
    simp only [not_le]
    exact Nat.lt_of_le_of_lt h (Nat.lt_add_one 1)
  · intro h x
    specialize h x
    exact Nat.le_of_lt_succ (Nat.lt_of_not_le h)

variable {α : Type*} [DecidableEq α]

lemma idxOf_append_left {v : α} {l₁ l₂ : List α}
    (hv : v ∈ l₁) :
    List.idxOf v (l₁ ++ l₂) = List.idxOf v l₁ := by
  induction l₁ with
  | nil => cases hv
  | cons x xs ih =>
    by_cases h : v = x
    · simp only [h, cons_append, idxOf_cons_self]
    · have hvxs : v ∈ xs := by simpa [h] using hv
      dsimp only [cons_append, idxOf]
      rw [← cons_append]
      simp only [cons_append, findIdx_cons]
      congr! 1; exact congrFun (congrArg HAdd.hAdd (ih hvxs)) 1

lemma ne_nil_of_head?_eq_some {α : Type*} {l : List α} {x : α} (h : l.head? = some x) : l ≠ [] := by
  by_contra heq
  rw [heq] at h
  simp only [head?_nil, reduceCtorEq] at h

/-- If `l₁` is a prefix of `l₂` and `v ∈ l₁` then the two
    indices of `v` coincide. -/
lemma idxOf_eq_idxOf_of_isPrefix {v : α} {l₁ l₂ : List α}
    (hpref : List.IsPrefix l₁ l₂) (hv : v ∈ l₁) :
    List.idxOf v l₂ = List.idxOf v l₁ := by
  rcases hpref with ⟨t, rfl⟩
  simpa using idxOf_append_left hv

namespace Nat
lemma eq_of_le_zero {n : ℕ} (h : n ≤ 0) : n = 0 :=
  le_antisymm h (Nat.zero_le _)
end Nat

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
      · (expose_names; (expose_names; refine List.getElem_idxOf (by exact List.idxOf_lt_length_of_mem hx)))
      · subst h_last
        simp_all only [getLast_mem, tsub_le_iff_right, le_add_iff_nonneg_right, le_refl, Nat.eq_of_le_zero, zero_le,
          inf_of_le_left]
    contradiction
  have h_idx_lt : l.idxOf x < l.length := List.idxOf_lt_length_of_mem hx
  exact Nat.le_antisymm (Nat.le_sub_one_of_lt h_idx_lt) h_idx_ge

@[simp] lemma not_gt {n m : ℕ} : (¬ n > m) ↔ n ≤ m := Nat.not_lt

omit [DecidableEq α] in
@[simp] lemma head_not_mem_tail_of_first
    {l : List α} (h : l.Nodup) (hne : l ≠ []) :
    l.head hne ∉ l.tail := by
  cases l with
  | nil        => cases hne rfl
  | cons hd tl =>
    simp only [List.nodup_cons] at h
    exact h.1

/-- Helper lemma for findIdx.go with accumulator incrementing by 1 -/
lemma findIdx_go_succ' {α : Type*} (p : α → Bool) (l : List α) (n : Nat) :
  findIdx.go p l (n+1) = findIdx.go p l n + 1 := by
  induction l generalizing n with
  | nil => rfl
  | cons hd tl ih =>
    simp only [findIdx.go]
    by_cases h_p : p hd = true
    · rw [ite_eq_left h_p, ite_eq_left h_p]
    · rw [ite_eq_right h_p, ite_eq_right h_p]
      exact ih (n+1)

/-- Helper lemma: the findIdx.go function with accumulator 1 returns the result of findIdx plus 1 -/
lemma findIdx_go_succ {α : Type*} (p : α → Bool) (l : List α) :
  findIdx.go p l 1 = findIdx p l + 1 := by
  unfold findIdx
  exact findIdx_go_succ' p l 0

omit [DecidableEq α] in
/-- Helper lemma: Boolean equality is false iff the terms are not equal -/
lemma beq_eq_false_iff_ne [DecidableEq α] {a b : α} : (a == b) = false ↔ a ≠ b := by
  rw [_root_.beq_eq_false_iff_ne]

omit [DecidableEq α] in
/-- Helper lemma for index computation with head != x -/
lemma idxOf_cons_of_ne [DecidableEq α] {hd : α} {tl : List α} {x : α} (h_neq : hd ≠ x) :
  idxOf x (hd :: tl) = idxOf x tl + 1 := by
  dsimp only [idxOf, findIdx]
  simp only [findIdx.go]
  have h_eq_false : (hd == x) = false := by
    rw [beq_eq_false_iff_ne]
    exact h_neq
  simp only [h_eq_false, Bool.false_eq_true, ite_false]
  exact findIdx_go_succ (fun y => y == x) tl

-- This helper lemma addresses many of the beq_iff_eq rewrite failures

/-- If `x` is in `l`, then getting the element at index `idxOf x l` gives `x`. -/
lemma get_idxOf_of_mem {l : List α} {x : α} (h : x ∈ l) :
  l.get ⟨idxOf x l, idxOf_lt_length_of_mem h⟩ = x := by
  induction l with
  | nil => simp only [not_mem_nil] at h
  | cons hd tl ih =>
    by_cases h_eq : hd = x
    · subst h_eq
      have h_idx : idxOf hd (hd :: tl) = 0 := by
        dsimp [idxOf, findIdx]
        simp only [findIdx.go]
        simp
      simp only [h_idx, get_eq_getElem, getElem_cons_zero]
    · simp only [mem_cons] at h
      cases h with
      | inl h_hd =>
        subst h_hd
        contradiction
      | inr h_tl =>
        have ih' := ih h_tl
        have h_idxOf : idxOf x (hd :: tl) = idxOf x tl + 1 := idxOf_cons_of_ne h_eq
        have hl : idxOf x tl < tl.length := idxOf_lt_length_of_mem h_tl
        have hl' : idxOf x tl + 1 < (hd :: tl).length := by
          rw [length_cons]
          exact Nat.add_lt_add_right hl 1
        have helper : (hd :: tl).get ⟨idxOf x (hd :: tl), idxOf_lt_length_of_mem (mem_cons.mpr (Or.inr h_tl))⟩ =
                      (hd :: tl).get ⟨idxOf x tl + 1, hl'⟩ := by
          congr
        have h_getElem : (hd :: tl).get ⟨idxOf x tl + 1, hl'⟩ = tl.get ⟨idxOf x tl, hl⟩ := by
          simp only [get_eq_getElem]
          apply getElem_cons_succ
        exact Eq.trans helper (Eq.trans h_getElem ih')

/-- Membership in the tail of `l.concat y`.
It is only useful if `l` is **non-empty** – we require `hl : l ≠ []`. -/
@[simp] lemma mem_tail_concat_of_ne_nil
    {α : Type*} {l : List α} (hl : l ≠ []) (x y : α) :
    x ∈ (l.concat y).tail ↔ x ∈ l.tail ∨ x = y := by
  cases l with
  | nil      => exact (hl rfl).elim
  | cons _ t => simp only [concat_eq_append, cons_append, tail_cons, mem_append, mem_cons,
    not_mem_nil, or_false]

/-- Membership in the tail of a concatenation splits into the two obvious
    alternatives. -/
lemma mem_tail_append {α : Type*} {x : α} {L₁ L₂ : List α} :
    x ∈ (L₁ ++ L₂).tail ↔ (L₁ = nil ∧ x ∈ L₂.tail) ∨ (L₁ ≠ nil ∧ x ∈ L₁.tail ++ L₂) := by
  cases L₁ with
  | nil =>
      simp only [tail, nil_append, true_and, ne_eq, not_true_eq_false, false_and, or_false]
  | cons h t =>
      simp only [tail, cons_append, mem_append, reduceCtorEq, false_and, ne_eq, not_false_eq_true,
        true_and, false_or]

@[simp]
lemma mem_of_mem_tail_dropLast {α} {x : α} {l : List α} :
    x ∈ (l.dropLast).tail → x ∈ l.tail := by
  cases l with
  | nil       => intro h; cases h
  | cons hd tl =>
      cases tl with
      | nil        => intro h; cases h
      | cons hd' tl' =>
          intro h
          have h' : x ∈ (hd' :: tl').dropLast := by
            simpa using h
          have : x ∈ (hd' :: tl') := List.mem_of_mem_dropLast h'
          simpa using this

/-- The last element of a list of length at least 2 is in its tail. -/
@[simp]
lemma getLast_mem_tail {α : Type*} {l : List α} (h : l.length ≥ 2) :
    l.getLast (List.ne_nil_of_length_pos (by linarith)) ∈ l.tail := by
  cases l with
  | nil => simp only [length_nil, le_refl, Nat.eq_of_le_zero, ge_iff_le, nonpos_iff_eq_zero,
    OfNat.ofNat_ne_zero] at h
  | cons hd tl =>
    have h_tl_len : tl.length ≥ 1 := Nat.le_of_succ_le_succ h
    have h_tl_nonempty : tl ≠ [] := List.ne_nil_of_length_pos (by linarith)
    simp only [tail_cons]
    simp_all only [ge_iff_le, ne_eq, not_false_eq_true, getLast_cons, getLast_mem]

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
      have hx_not_mem : x ∉ xs := (disjoint_singleton_right).1 h_disj
      simpa using hx_not_mem

omit [DecidableEq α] in
@[simp] lemma getLast_not_mem_dropLast
   {l : List α} (h_ne : l ≠ []) (h_nodup : l.Nodup) :
    l.getLast h_ne ∉ l.dropLast := by
  simpa using List.not_mem_dropLast_getLast (l := l) h_ne h_nodup

end List
