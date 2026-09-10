import Mathlib.Algebra.Group.ForwardDiff

/-!
# Causal forward differences

This file records the forward-difference convention for sequences indexed by
natural numbers which retains the initial value.
-/

namespace Function

/-- The forward difference with its initial value retained. This is the
causal difference convention for sequences indexed by `ℕ`. -/
def causalFwdDiff {R : Type*} [Sub R] (a : ℕ → R) : ℕ → R
  | 0 => a 0
  | n + 1 => a (n + 1) - a n

end Function
