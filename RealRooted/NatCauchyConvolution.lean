import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Range

open scoped BigOperators

namespace RealRooted

/-- Cauchy convolution of two sequences indexed by the natural numbers. -/
def natCauchyConvolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

end RealRooted
