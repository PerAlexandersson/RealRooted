/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.List.Sort

/-!
# Upper endpoints of sorted lists

This file records the endpoint decomposition of a sorted list bounded above by
one of its values.
-/

namespace List

variable {α : Type*} [PartialOrder α] [DecidableEq α]

/-- A sorted list all of whose entries are at most `a` consists of its entries
different from `a`, followed by all its copies of `a`. -/
lemma eq_filter_ne_append_replicate_count {l : List α} {a : α}
    (hsorted : l.Pairwise (· ≤ ·)) (hupper : ∀ x ∈ l, x ≤ a) :
    l = l.filter (fun x ↦ decide (x ≠ a)) ++ List.replicate (l.count a) a := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [pairwise_cons] at hsorted
      have hsorted' := hsorted.2
      have hupper' : ∀ x ∈ l, x ≤ a := by
        intro x hx
        exact hupper x (mem_cons_of_mem _ hx)
      by_cases hb : b = a
      · subst b
        have hendpoint : ∀ x ∈ l, x = a := by
          intro x hx
          exact le_antisymm (hupper' x hx) (hsorted.1 x hx)
        have hfilter : l.filter (fun x ↦ decide (x ≠ a)) = [] := by
          rw [filter_eq_nil_iff]
          grind
        grind
      · grind

end List
