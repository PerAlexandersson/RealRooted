module

public import RealRooted.Tactic.RowInterlacing
public import RealRooted.Tactic.Examples.RowFixtures
public import RealRooted.Tactic.Examples.RowInterlacing

/-!
# Row interlacing examples: products, Euler steps, windows, hinted splits

Regression tests for the row tactics on products, half growth with a common lag root, derivative
lags, general Euler steps, moving root windows and hinted calls of `rr_row_splits`; split from
`RowInterlacing` so that the example files build in parallel.
-/

@[expose] public section

open Polynomial
open RealRooted.Tactic.RowFixtures

namespace RealRooted.Tactic.RowInterlacingExamples

noncomputable section

/-! ### Products, half growth with a common lag root, derivative lags -/

/-- A derivative-lag recurrence `P (n + 2) = U P (n + 1) + V P' (n + 1) + W P n` with
`V ≤ 0`, `W < 0` on the negative axis (A144436). -/
def A144436 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (C 1 * X + C (-1) * X ^ 2) * (A144436 (n + 1)).derivative +
      (C 1 + C (2 + (n : ℝ)) * X) * A144436 (n + 1) + (C 4 * X) * A144436 n

theorem A144436_splits (n : ℕ) : (A144436 n).Splits := by rr_row_splits

/-- A derivative-lag recurrence with half growth (A008299). -/
def A008299 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => (C 1 * X) * (A008299 (n + 1)).derivative + C 1 * A008299 (n + 1) +
      (C (3 + (n : ℝ)) * X) * A008299 n

theorem A008299_splits (n : ℕ) : (A008299 n).Splits := by rr_row_splits

/-- Half growth whose lags `(n + 1) (X - 1)` share the root `1`
(`RealRooted.eval_mul_eval_nonneg_of_natDegree_le_one`) (A136394). -/
def A136394 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => C (2 + (n : ℝ)) * A136394 (n + 1) + (C (-1 + -1 * (n : ℝ)) + C (1 + (n : ℝ)) * X) *
      A136394 n

theorem A136394_splits (n : ℕ) : (A136394 n).Splits := by rr_row_splits

/-- A product with a real-rooted quadratic factor (A272866). -/
def A272866 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X ^ 2 + 3 * X) * A272866 n

theorem A272866_splits (n : ℕ) : (A272866 n).Splits := by rr_row_splits

/-- A product with a cubic first row. -/
def cubicShiftRows : ℕ → ℝ[X]
  | 0 => 1 + 3 * X + 3 * X ^ 2 + X ^ 3
  | n + 1 => X * cubicShiftRows n

theorem cubicShiftRows_splits (n : ℕ) : (cubicShiftRows n).Splits := by rr_row_splits
theorem cubicShiftRows_interlaces (n : ℕ) :
    Interlaces (cubicShiftRows n) (cubicShiftRows (n + 1)) := by
  rr_row_interlaces

/-- Half growth whose lag coefficients are quadratic in `n` (A306364). -/
def A306364 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3
  | n + 2 => C (5 + 2 * (n : ℝ)) * A306364 (n + 1) +
      (C (6 + -1 * (3 + (n : ℝ)) ^ 2 + 2 * (n : ℝ)) +
        C (-6 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ)) * X) * A306364 n

theorem A306364_splits (n : ℕ) : (A306364 n).Splits := by rr_row_splits

/-- A two-step product `P (n + 2) = (1 + 2 X) P n` (A188440). -/
def A188440 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => (1 + 2 * X) * A188440 n

theorem A188440_splits (n : ℕ) : (A188440 n).Splits := by rr_row_splits

/-- A two-step product with a double root `q = X ^ 2` (A133080). -/
def A133080 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => X ^ 2 * A133080 n

theorem A133080_splits (n : ℕ) : (A133080 n).Splits := by rr_row_splits

/-- A product read off `P (n + 3) = X * P (n + 2)` (A167194). -/
def A167194 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | 2 => 1 + 2 * X + X ^ 2
  | n + 3 => X * A167194 (n + 2)

theorem A167194_splits (n : ℕ) : (A167194 n).Splits := by rr_row_splits

/-- Half growth after the zero row `P 0 = 0` (A180047). -/
def A180047 : ℕ → ℝ[X]
  | 0 => 0
  | 1 => X
  | n + 2 => C (2 + (n : ℝ)) * A180047 (n + 1) + (C 1 * X) * A180047 n

theorem A180047_splits (n : ℕ) : (A180047 n).Splits := by rr_row_splits

/-! ### General Euler steps

Second-order recurrences `P (n + 1) = κX² (P n)'' + (κ(a + b + 1)X + vX²) (P n)' +
(κab + (u₀ + s n) X) P n` with no eigen-ODE, through
`RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec`. -/

/-- Central factorial numbers: `κ = a = b = 1`, `v = 0` (A036969). -/
def A036969 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (A036969 n).derivative.derivative + (3 * X) * (A036969 n).derivative +
      (1 + X) * A036969 n

theorem A036969_interlaces (n : ℕ) : Interlaces (A036969 n) (A036969 (n + 1)) := by
  rr_row_interlaces
theorem A036969_splits (n : ℕ) : (A036969 n).Splits := by rr_row_splits

theorem A160562_splits (n : ℕ) : (A160562 n).Splits := by rr_row_splits

/-- `κ = 2`, `a = 1 / 2`, `b = 1`, `v = -2` and `u n = 1 + 2n` (A166961). -/
def A166961 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 2 * X ^ 2) * (A166961 n).derivative.derivative +
      (C 5 * X + C (-2) * X ^ 2) * (A166961 n).derivative +
      (C 1 + C (1 + 2 * (n : ℝ)) * X) * A166961 n

theorem A166961_interlaces (n : ℕ) : Interlaces (A166961 n) (A166961 (n + 1)) := by
  rr_row_interlaces

/-- `θ ^ 2 + X`, the Euler step with `a = b = 0`: from `P 1` on the rows carry the factor `X`
(A269945, `RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec_zero`). -/
def A269945 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (A269945 n).derivative.derivative + X * (A269945 n).derivative +
      X * A269945 n

theorem A269945_interlaces (n : ℕ) : Interlaces (A269945 n) (A269945 (n + 1)) := by
  rr_row_interlaces

#guard_msgs (drop info) in
example (n : ℕ) : Interlaces (A166961 n) (A166961 (n + 1)) := by
  rr_row_interlaces?

/-! ### Moving root windows -/

/-- The roots stay in `[L n, 0]`, where `L n = -(8n + 21) / (9n + 24)` is the other root of
`A n` and decreases with `n` (A370258,
`RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_div`). -/
def A370258 : ℕ → ℝ[X]
  | 0 => 1 + 10 * X + 15 * X ^ 2
  | n + 1 =>
      (C ((21 / 2 + 4 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X +
          C ((12 + 9 / 2 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X ^ 2) *
        (A370258 n).derivative +
      (C 1 + C ((24 + 9 * (2 + (n : ℝ)) ^ 2 + 21 / 2 * n) /
          (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X) * A370258 n

theorem A370258_interlaces (n : ℕ) : Interlaces (A370258 n) (A370258 (n + 1)) := by
  rr_row_interlaces

/-- The roots stay at most `U n = -(n + 3) / (8n + 21)`, the smaller root of `A n`, which
increases with `n`; the other root `1` of `A n` splits the conditions beyond `U (n + 1)`
(A110608, `RealRooted.derivativeRecurrence_interlaces_of_roots_le_mono_div`). -/
def A110608 : ℕ → ℝ[X]
  | 0 => 6 + 8 * X + X ^ 2
  | n + 1 =>
      (C ((3 / 2 + (n : ℝ) / 2) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) +
          C ((9 + 7 / 2 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X +
          C ((-21 / 2 - 4 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X ^ 2) *
        (A110608 n).derivative +
      (C ((18 + 8 * (n : ℝ) + 15 / 2 * (2 + (n : ℝ)) ^ 2) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) +
          C ((12 + 6 * (2 + (n : ℝ)) ^ 2 + 11 / 2 * n) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) *
            X) * A110608 n

theorem A110608_interlaces (n : ℕ) : Interlaces (A110608 n) (A110608 (n + 1)) := by
  rr_row_interlaces

theorem A110608_splits (n : ℕ) : (A110608 n).Splits := by rr_row_splits

/-! ### Hinted calls of `rr_row_splits` -/

/--
info: Try these:
  [apply] rr_row_splits (via := nextRow)
        (thm := RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc) (degree := 0) (drop := 0)
        (window := [-1, 0])
-/
#guard_msgs in
example (n : ℕ) : (A019538 n).Splits := by
  rr_row_splits?

/--
info: Try these:
  [apply] rr_row_splits (drop := 1) (half := 1)
-/
#guard_msgs in
example (n : ℕ) : (A008299 n).Splits := by
  rr_row_splits?

example (n : ℕ) : (A008299 n).Splits := by rr_row_splits (drop := 1) (half := 1)
example (n : ℕ) : (A180047 n).Splits := by rr_row_splits (via := halfGrowth) (drop := 1)
example (n : ℕ) : (A008292 n).Splits := by rr_row_splits
example (n : ℕ) : (A133080 n).Splits := by rr_row_splits (via := twoStep)
example (n : ℕ) : (A167194 n).Splits := by rr_row_splits
example (n : ℕ) : (swappedProduct n).Splits := by rr_row_splits (via := linearFactors)
example (n : ℕ) : (swappedProduct n).Splits := by rr_row_splits (via := splitFactors)

/--
error: rr_row_splits: unknown route foo; the routes are
affineCoefficient, variableDelay, derivativeXMul, factorPower, delayedProduct,
closedForm, halfGrowth, pathPower, lowerOrder, thresholdOrbit, parityProduct,
lagFeedback, subseq, linearFactors, splitFactors, twoStep, nextRow, degreePattern,
reversed, fTransform
-/
#guard_msgs (whitespace := normalized) in
example (n : ℕ) : (A008292 n).Splits := by rr_row_splits (via := foo)

end

end RealRooted.Tactic.RowInterlacingExamples
