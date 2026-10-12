import RealRooted.Tactic.RowInterlacing

/-!
# Cancellation and invariant-cone degree routes

These four regressions exercise the theorem-backed `rr_row_natDegree` routes.  Against
`origin/main` before this patch, the cancellation rows already closed through the legacy
specialized fallback, but `(via := cancel)` did not select a route and the final certificate
did not use the general `LinRec` cancellation theorem.  The two cone examples ended with
`rr_linrec: no regime`.  The first cone probe finds the forms
`c n`, `c (n + 1) - c n`, and `c (n + 2) - 3 c (n + 1) + 2 c n`; the second finds
`c n`, its first difference, and two consecutive second differences.
-/

open Polynomial

namespace RealRooted.Tactic.RowDegreeRoutes

noncomputable section

/-- A first-order derivative recurrence with cancellation at every step. -/
def cancelLinear : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X - X ^ 3) * (cancelLinear n).derivative +
      (1 + 2 * X + C (n : ℝ) * X ^ 2) * cancelLinear n

/-- A first-order derivative recurrence whose leading terms cancel on alternating steps. -/
def cancelHalf : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X - 2 * X ^ 2) * (cancelHalf n).derivative +
      (1 + C (n : ℝ) * X) * cancelHalf n

/-- Monomial rows whose leading coefficients have characteristic roots `1`, `2`, and `4`. -/
def coneOneTwoFour : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 9 * X
  | 2 => 49 * X ^ 2
  | n + 3 => 7 * X * coneOneTwoFour (n + 2) -
      14 * X ^ 2 * coneOneTwoFour (n + 1) + 8 * X ^ 3 * coneOneTwoFour n

/-- Monomial rows whose leading coefficients are `Nat.fib (n + 5) - n - 4`. -/
def coneFibSubLinear : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 * X
  | 2 => 7 * X ^ 2
  | 3 => 14 * X ^ 3
  | n + 4 => 3 * X * coneFibSubLinear (n + 3) -
      2 * X ^ 2 * coneFibSubLinear (n + 2) -
      X ^ 3 * coneFibSubLinear (n + 1) + X ^ 4 * coneFibSubLinear n

example (n : ℕ) : (cancelLinear n).natDegree = n := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (cancelHalf n).natDegree = n / 2 := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (coneOneTwoFour n).natDegree = n := by
  rr_row_natDegree (via := cone)

example (n : ℕ) : (coneFibSubLinear n).natDegree = n := by
  rr_row_natDegree (via := cone)

end

end RealRooted.Tactic.RowDegreeRoutes
