module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Shared row fixtures

Recursive polynomial rows shared by the tactic regression modules.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowFixtures

noncomputable section

/-- Stirling numbers of the second kind (A008277). -/
def A008277 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * (A008277 n).derivative + (1 + X) * A008277 n

/-- A second-order derivative recurrence (A160562). -/
def A160562 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (4 * X ^ 2) * (A160562 n).derivative.derivative +
      (8 * X) * (A160562 n).derivative + (1 + X) * A160562 n

/-- The top multiplier vanishes in the first step, so the degree is `n - 1`
(A055356). -/
def A055356 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X) * (A055356 n).derivative + (C 1 + C (n : ℝ) * X) * A055356 n

/-- A three-term recurrence with offset three and explicit rows `0, 1, 2`, whose degree
multiplier ratio is `1` (A084534). -/
def A084534 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | 2 => 1 + 4 * X + 2 * X ^ 2
  | n + 3 => ((1 + (2 * X))) * A084534 (n + 2) + ((-1 * (X) ^ (2))) * A084534 (n + 1)

/-- Offset three with nonnegative coefficients (A102413). -/
def A102413 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | n + 3 => ((1 + X)) * A102413 (n + 2) + (X) * A102413 (n + 1)

/-- Offset three with `b = -(1 + X) ^ 2` (A103450). -/
def A103450 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 3 * X + X ^ 2
  | n + 3 => ((2 + (2 * X))) * A103450 (n + 2) +
      ((-1 + (-1 * (X) ^ (2)) + (-2 * X))) * A103450 (n + 1)

/-- A three-term recurrence with the summands and factors in another order. -/
def swappedLag : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => X * swappedLag n + swappedLag (n + 1) * (1 + X)

/-- A subtracted summand (the rows of A056241). -/
def subtractedLag : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (2 + 2 * X) * subtractedLag (n + 1) - (1 + X + X ^ 2) * subtractedLag n

/-- A first-order recurrence with the derivative summand last (the rows of A008277). -/
def swappedDeriv : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * swappedDeriv n + X * (swappedDeriv n).derivative

/-- A product with the factor on the right. -/
def swappedProduct : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => swappedProduct n * (2 + X)

/-- Periodic growth with period four and a lag of changing sign (A118884). -/
def A118884 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | n + 4 => 2 * A118884 (n + 3) + (-1 + X) * A118884 n

/-- A product with the derivative, `P (n + 1) = A * (P n)'` (A142071). -/
def A142071 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (X + X ^ 2) * (A142071 (n + 1)).derivative

end

end RealRooted.Tactic.RowFixtures
