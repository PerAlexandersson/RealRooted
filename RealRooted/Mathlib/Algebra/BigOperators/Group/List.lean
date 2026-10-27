/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Sums over `List.range`

A sum of `f` over `List.range n` is the `Finset.range n` sum of `f`, and sums over
`List.range' k (q - k)` or a dropped prefix of `List.range q` are `Finset.Ico k q` sums.
-/

public section

namespace List

theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ, List.map_singleton, List.sum_singleton]

theorem sum_map_range'_eq_sum_Ico {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k q : ℕ) :
    ((List.range' k (q - k)).map f).sum = ∑ j ∈ Finset.Ico k q, f j := by
  rw [Finset.sum_Ico_eq_sum_range, List.range'_eq_map_range, List.map_map, sum_map_range]
  simp [Function.comp_apply]

theorem sum_drop_map_range_eq_sum_Ico {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k q : ℕ) :
    (((List.range q).map f).drop k).sum = ∑ j ∈ Finset.Ico k q, f j := by
  rw [← List.map_drop, show List.range q = List.range' 0 q from List.range_eq_range',
    List.drop_range']
  simpa using sum_map_range'_eq_sum_Ico f k q

end List
