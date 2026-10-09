import RealRooted.EulerBidiagonal

/-!
# Central factorial and Legendre–Stirling rows interlace

The row polynomials of the central factorial numbers (OEIS A036969,
`P (n+1) = X² P'' + 3 X P' + (1 + X) P`) and of the Legendre–Stirling numbers (OEIS A071951) are
the rows of the bidiagonal Euler step `X + (θ + a)(θ + b)` with `(a, b) = (1, 1)` and `(1, 2)`.
Hence consecutive rows strictly interlace (`EulerBidiagonal.strictInterl_rows`).
-/

open Polynomial

namespace RealRooted

open EulerBidiagonal

noncomputable section

/-- The central-factorial recurrence from OEIS A036969. -/
def centralFactorialRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X ^ 2 * (centralFactorialRows n).derivative.derivative +
        3 * X * (centralFactorialRows n).derivative +
        (1 + X) * centralFactorialRows n

/-- The A036969 recurrence is the (a,b)=(1,1) Euler step. -/
theorem centralFactorialRows_eq_rows (n : ℕ) :
    centralFactorialRows n = rows 1 1 n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [centralFactorialRows, rows, ih, step_eq_second_derivative]
      norm_num [C_ofNat]

/-- Consecutive central-factorial rows strictly interlace. -/
theorem strictInterl_centralFactorialRows (n : ℕ) :
    StrictInterl (centralFactorialRows n) (centralFactorialRows (n + 1)) ∧
      ∀ r, ¬ ((centralFactorialRows n).IsRoot r ∧
        (centralFactorialRows (n + 1)).IsRoot r) := by
  rw [centralFactorialRows_eq_rows n, centralFactorialRows_eq_rows (n + 1)]
  exact strictInterl_rows (by norm_num) (by norm_num) (by norm_num) n

example : centralFactorialRows 0 = 1 := by
  rfl

example : centralFactorialRows 1 = 1 + X := by
  norm_num [centralFactorialRows]

example : centralFactorialRows 2 = 1 + 5 * X + X ^ 2 := by
  norm_num [centralFactorialRows]
  ring

/-- The Legendre--Stirling recurrence from OEIS A071951. -/
def legendreStirlingRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X ^ 2 * (legendreStirlingRows n).derivative.derivative +
        4 * X * (legendreStirlingRows n).derivative +
        (2 + X) * legendreStirlingRows n

/-- The A071951 recurrence is the (a,b)=(1,2) Euler step. -/
theorem legendreStirlingRows_eq_rows (n : ℕ) :
    legendreStirlingRows n = rows 1 2 n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [legendreStirlingRows, rows, ih, step_eq_second_derivative]
      norm_num [C_ofNat]

/-- Consecutive Legendre--Stirling rows strictly interlace. -/
theorem strictInterl_legendreStirlingRows (n : ℕ) :
    StrictInterl (legendreStirlingRows n) (legendreStirlingRows (n + 1)) ∧
      ∀ r, ¬ ((legendreStirlingRows n).IsRoot r ∧
        (legendreStirlingRows (n + 1)).IsRoot r) := by
  rw [legendreStirlingRows_eq_rows n, legendreStirlingRows_eq_rows (n + 1)]
  exact strictInterl_rows (by norm_num) (by norm_num) (by norm_num) n

example : legendreStirlingRows 0 = 1 := by
  rfl

example : legendreStirlingRows 1 = 2 + X := by
  norm_num [legendreStirlingRows]

example : legendreStirlingRows 2 = 4 + 8 * X + X ^ 2 := by
  norm_num [legendreStirlingRows]
  ring

end

end RealRooted
