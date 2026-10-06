module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sums over `List.range`

A sum of `f` over `List.range n` is the `Finset.range n` sum of `f`.
-/

public section

namespace List

theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ, List.map_singleton, List.sum_singleton]

end List
