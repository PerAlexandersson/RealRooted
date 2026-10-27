module

public import RealRooted.Applications.OEIS.A359363
public import RealRooted.CombinatorialExamples.Motzkin
public import RealRooted.CombinatorialExamples.Simsun
public import RealRooted.CombinatorialExamples.SingletonFreeSetPartitions
public import RealRooted.Tactic.RowInterlacing

/-!
# Equal-degree strict row interlacing

Regression examples for `rr_row_strictInterl` on half-growth three-term,
derivative-lag and first-order derivative recurrences.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowStrictInterlExamples

noncomputable section

/-! ## Small half-growth recurrence -/

/-- Fibonacci polynomials, including equal-degree consecutive rows. -/
def fibonacciRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => fibonacciRows (n + 1) + X * fibonacciRows n

example (n : ℕ) : StrictInterl (fibonacciRows n) (fibonacciRows (n + 1)) := by
  rr_row_strictInterl

/-! ## Combinatorial families -/

example (n : ℕ) : StrictInterl (motzkin n) (motzkin (n + 1)) := by
  rr_row_strictInterl

example (n : ℕ) :
    StrictInterl (singletonFreeSetPartitions (n + 2))
      (singletonFreeSetPartitions (n + 3)) := by
  rr_row_strictInterl

example (n : ℕ) : StrictInterl (simsun n) (simsun (n + 1)) := by
  rr_row_strictInterl

/-! ## General interlacing fallback -/

example (n : ℕ) :
    StrictInterl (Applications.OEIS.A359363.polynomial n)
      (Applications.OEIS.A359363.polynomial (n + 1)) := by
  rr_row_strictInterl

/-! ## Negative tests -/

/-- The first pair has equal degree but the root orientation is reversed. -/
def reversedBaseRows : ℕ → ℝ[X]
  | 0 => 1 + 2 * X
  | 1 => 1 + X
  | n + 2 => reversedBaseRows (n + 1) + X * reversedBaseRows n

example : True := by
  fail_if_success
    have _ : ∀ n, StrictInterl (reversedBaseRows n) (reversedBaseRows (n + 1)) := by
      rr_row_strictInterl
  trivial

/-- Its degree jumps by two at each step, outside the `StrictInterl` degree range. -/
def degreeGapTwoRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X ^ 2) * degreeGapTwoRows n

example : True := by
  fail_if_success
    have _ : ∀ n, StrictInterl (degreeGapTwoRows n) (degreeGapTwoRows (n + 1)) := by
      rr_row_strictInterl
  trivial

end

end RealRooted.Tactic.RowStrictInterlExamples
