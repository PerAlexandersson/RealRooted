/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Shifting finite sums with vanishing boundary terms
-/

public section

namespace Finset

variable {M : Type*} [AddCommMonoid M]

/-- Two sums over the same range agree when their terms are shifted by one and the omitted
boundary terms vanish. -/
theorem sum_range_shift {U V : ℕ → M} (n : ℕ) (hU0 : U 0 = 0) (hVn : V n = 0)
    (h : ∀ i, U (i + 1) = V i) :
    ∑ i ∈ range (n + 1), U i = ∑ i ∈ range (n + 1), V i := by
  conv_lhs => rw [sum_range_succ']
  conv_rhs => rw [sum_range_succ]
  rw [hU0, hVn, add_zero, add_zero]
  exact sum_congr rfl fun i _ ↦ h i

end Finset
