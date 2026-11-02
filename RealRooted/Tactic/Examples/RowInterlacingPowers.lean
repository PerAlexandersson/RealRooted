module

public import RealRooted.Tactic.RowInterlacing
public import RealRooted.Tactic.Examples.RowFixtures

/-!
# Row interlacing examples: power rows and the `f`-polynomial transform

Regression tests for the row tactics on rows `c m · q ^ m` and on the `f`-polynomial transform;
split from `RowInterlacing` so that the example files build in parallel.
-/

@[expose] public section

open Polynomial
open RealRooted.Tactic.RowFixtures

namespace RealRooted.Tactic.RowInterlacingExamples

noncomputable section

/-! ### Rows `c m · q ^ m`

Recurrences whose multipliers are powers of one linear `q`
(`RealRooted.interlaces_of_forall_eq_C_mul_pow`). -/

/-- `P (n + 2) = X P (n + 1) + X ^ 2 P n` (A127647). -/
def A127647 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * A127647 (n + 1) + X ^ 2 * A127647 n

theorem A127647_interlaces (n : ℕ) : Interlaces (A127647 n) (A127647 (n + 1)) := by
  rr_row_interlaces

/-- The order-three recurrence with characteristic polynomial `(t - (1 + X)) ^ 3` (A094305). -/
def A094305 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 + 3 * X
  | 2 => 6 + 12 * X + 6 * X ^ 2
  | n + 3 => (3 + 3 * X) * A094305 (n + 2) + (-3 + -6 * X + -3 * X ^ 2) * A094305 (n + 1) +
      (1 + X ^ 3 + 3 * X + 3 * X ^ 2) * A094305 n

theorem A094305_interlaces (n : ℕ) : Interlaces (A094305 n) (A094305 (n + 1)) := by
  rr_row_interlaces

/-- Multipliers `(2n + 3) / (n + 2) · (1 + X)` and `3 (n + 1) / (n + 2) · (1 + X) ^ 2`, rational in
`n` and nonnegative, so that the rows never vanish (A376827). -/
def A376827 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => C ((2 * (n : ℝ) + 3) / (n + 2)) * (1 + X) * A376827 (n + 1) +
      C (3 * ((n : ℝ) + 1) / (n + 2)) * (1 + X) ^ 2 * A376827 n

theorem A376827_interlaces (n : ℕ) : Interlaces (A376827 n) (A376827 (n + 1)) := by
  rr_row_interlaces

/-- The reversed rows of `X ^ 3 P'' - (2n + 1) X ^ 2 P' + (1 + (n + 1) ^ 2 X) P` satisfy
`R (n + 1) = X ^ 2 R'' + 3 X R' + (1 + X) R`, an Euler step: the route through the reversed
rows (A008957, central factorial numbers). -/
def A008957 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C 1 * X ^ 3 * (A008957 n).derivative.derivative +
      C (-1 - 2 * (n : ℝ)) * X ^ 2 * (A008957 n).derivative +
      (C 1 + C (((n : ℝ) + 1) ^ 2) * X) * A008957 n

theorem A008957_interlaces (n : ℕ) : Interlaces (A008957 n) (A008957 (n + 1)) := by
  rr_row_interlaces

theorem A008957_splits (n : ℕ) : (A008957 n).Splits := by
  rr_row_splits

/-- Reversed rows again (A191935). -/
def A191935 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C 1 * X ^ 3 * (A191935 n).derivative.derivative +
      C (-2 - 2 * (n : ℝ)) * X ^ 2 * (A191935 n).derivative +
      (C 1 + C (-2 + (2 + (n : ℝ)) ^ 2 - (n : ℝ)) * X) * A191935 n

theorem A191935_interlaces (n : ℕ) : Interlaces (A191935 n) (A191935 (n + 1)) := by
  rr_row_interlaces

/-- Order three with characteristic polynomial `(z + 1) (z ^ 2 - (X + 2) z + 1)`: the rows are
`s m * t m` and `s (m + 1) * t m` for two solutions of `x (m + 2) = (X + 2) x (m + 1) - x m`
(A158909). -/
def A158909 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + 1
  | 2 => X ^ 2 + 3 * X + 2
  | n + 3 => (X + 1) * A158909 (n + 2) + (X + 1) * A158909 (n + 1) - A158909 n

theorem A158909_interlaces (n : ℕ) : Interlaces (A158909 n) (A158909 (n + 1)) := by
  rr_row_interlaces

theorem A158909_splits (n : ℕ) : (A158909 n).Splits := by
  rr_row_splits

/-- A parity product with `μ = -X` and `β = 2 X + 1` (A092879). -/
def A092879 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + 1
  | 2 => 2 * X ^ 2 + 3 * X + 1
  | n + 3 => (X + 1) * A092879 (n + 2) + (X + X ^ 2) * A092879 (n + 1) - X ^ 3 * A092879 n

theorem A092879_interlaces (n : ℕ) : Interlaces (A092879 n) (A092879 (n + 1)) := by
  rr_row_interlaces

/-- `P (n + 3) = P (n + 2) + 3 X P n`: windows of three rows stay interlacing (A317496). -/
def A317496 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => (1) * A317496 (n + 2) + 3 * X * A317496 n

theorem A317496_splits (n : ℕ) : (A317496 n).Splits := by
  rr_row_splits

/-- A feedback coefficient depending on `n` (A118931). -/
def A118931 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => C 1 * A118931 (n + 2) + C (-14 + (4 + (n : ℝ)) ^ 2 - 5 * (n : ℝ)) * X * A118931 n

theorem A118931_splits (n : ℕ) : (A118931 n).Splits := by
  rr_row_splits

theorem A118884_splits (n : ℕ) : (A118884 n).Splits := by
  rr_row_splits

/-- The rows `P m = m (1 + X) X ^ (m - 1)` start the power form after the row `P 0 = 1`
(A128540). -/
def A128540 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 2 * X + 2 * X ^ 2
  | n + 3 => X * A128540 (n + 2) + X ^ 2 * A128540 (n + 1)

theorem A128540_interlaces (n : ℕ) : Interlaces (A128540 n) (A128540 (n + 1)) := by
  rr_row_interlaces

/-- Chebyshev-like rows: `b n = -(1 + X)` is negative beyond the window `[-1, 0]`, and the
ratio barrier `ρ = 1` keeps the rows positive there (A056242). -/
def A056242 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 => (2 + 2 * X) * A056242 (n + 1) + (-1 - X) * A056242 n

theorem A056242_interlaces (n : ℕ) : Interlaces (A056242 n) (A056242 (n + 1)) := by
  rr_row_interlaces

theorem A056242_splits (n : ℕ) : (A056242 n).Splits := by
  rr_row_splits

/-- The ratio barrier `ρ = 2` beyond the window `[-4, 0]`, after the first row (A236471). -/
def A236471 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 2 + 4 * X + X ^ 2
  | n + 3 => (4 + X) * A236471 (n + 2) + (-4 - X) * A236471 (n + 1)

theorem A236471_interlaces (n : ℕ) : Interlaces (A236471 n) (A236471 (n + 1)) := by
  rr_row_interlaces

theorem A142071_interlaces (n : ℕ) : Interlaces (A142071 n) (A142071 (n + 1)) := by
  rr_row_interlaces

/-! ### The `f`-polynomial transform

The alternating-runs rows (A186370) are `fPolynomial n (Q n)` for the peak-type rows
`Q (n + 1) = (t - 2t²) Q n' + (1 + n t) Q n`, whose degree grows by half a step
(`Row.FTransform`). -/

/-- Alternating runs (A186370). -/
def A186370 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X - X ^ 3) * (A186370 n).derivative + (1 + X + C (n : ℝ) * X ^ 2) * A186370 n

theorem A186370_splits (n : ℕ) : (A186370 n).Splits := by rr_row_splits

/-- Rows `X ^ n * R n` with `R n` quadratic, from an order-three recurrence with characteristic
polynomial `(λ - X)³` (A106246): consecutive rows interlace by a division-remainder certificate. -/
def A106246 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | 2 => 1 + 4 * X + X ^ 2
  | n + 3 => 3 * X * A106246 (n + 2) + (-3 * X ^ 2) * A106246 (n + 1) + X ^ 3 * A106246 n

theorem A106246_interlaces (n : ℕ) : Interlaces (A106246 n) (A106246 (n + 1)) := by
  rr_row_interlaces

/-- Order three, rows are orbit sums of the Haglund–Zhang threshold matrix with rows
`(1, 1), (2, 1), (3, 1)` on the input `[1, 0, 0]` (A120987). -/
def A120987 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 * X
  | 2 => 3 * X + 6 * X ^ 2
  | n + 3 => ((3 * X)) * A120987 (n + 2) + (((-3 * (X) ^ (2)) + (3 * X))) * A120987 (n + 1)
      + ((X + (X) ^ (3) + (-2 * (X) ^ (2)))) * A120987 n

theorem A120987_splits (n : ℕ) : (A120987 n).Splits := by
  rr_row_splits

/-- Order three, rows shifted by one are orbit sums of a Gustafsson–Solus threshold matrix
(A304429). -/
def A304429 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1 + X
  | n + 3 => (3) * A304429 (n + 2) + ((-3 + (2 * X))) * A304429 (n + 1) + ((1
      + (-1 * X))) * A304429 n

theorem A304429_splits (n : ℕ) : (A304429 n).Splits := by
  rr_row_splits

/-- Order three with characteristic polynomial `(λ - (1 + X))³` and a palindromic quartic
residual (A124376): the rows are `(1 + X) ^ m` times `X⁴ + b X³ + c X² + b X + 1`. -/
def A124376 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | 3 => 1 + 7 * X + 7 * X ^ 2 + X ^ 3
  | 4 => 1 + 10 * X + 19 * X ^ 2 + 10 * X ^ 3 + X ^ 4
  | n + 5 => ((3 + (3 * X))) * A124376 (n + 4) + ((-3 + (-6 * X)
      + (-3 * (X) ^ (2)))) * A124376 (n + 3) + ((1 + (X) ^ (3) + (3 * X)
      + (3 * (X) ^ (2)))) * A124376 (n + 2)

theorem A124376_splits (n : ℕ) : (A124376 n).Splits := by
  rr_row_splits

/-- An order-three recurrence with characteristic polynomial `(λ - (1 + X))³` and linear
residuals (A124932). -/
def A124932 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 3 * X
  | 2 => 3 + 9 * X + 6 * X ^ 2
  | n + 3 => (3 + 3 * X) * A124932 (n + 2) + (-3 - 6 * X - 3 * X ^ 2) * A124932 (n + 1) +
      (1 + 3 * X + 3 * X ^ 2 + X ^ 3) * A124932 n

theorem A124932_interlaces (n : ℕ) : Interlaces (A124932 n) (A124932 (n + 1)) := by
  rr_row_interlaces

end

end RealRooted.Tactic.RowInterlacingExamples
