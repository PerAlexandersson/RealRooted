module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Range

@[expose] public section

open scoped BigOperators

namespace RealRooted

/-- Cauchy convolution of two sequences indexed by the natural numbers. -/
def natCauchyConvolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

end RealRooted
