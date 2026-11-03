/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Splitting a sum over `range (2 * m)` into consecutive pairs
-/

public section

namespace Finset

variable {M : Type*} [AddCommMonoid M]

/-- A sum over `range (2 * m)` is the sum over `range m` of the pairs of consecutive terms. -/
theorem sum_range_two_mul (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by lia, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

end Finset
