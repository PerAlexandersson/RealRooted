module

public import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Cancellation with a nonzero coefficient-ratio bound

These regressions copy seven recurrences from the downstream OEIS project.  The
`A101343` example requires the exact rows-zero-through-eight fit `rho = 1`.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowCancelRho

noncomputable section

/-- The recurrence defining the A008303 row polynomials. -/
def A008303 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 2 * X + C (-2) * X ^ 2) * (A008303 n).derivative +
        (C 2 + C (n : ℝ) * X) * A008303 n

/-- The recurrence defining the A008971 row polynomials. -/
def A008971 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 2 * X + C (-2) * X ^ 2) * (A008971 n).derivative +
        (C 1 + C (n : ℝ) * X) * A008971 n

/-- The recurrence defining the A059427 row polynomials. -/
def A059427 : ℕ → ℝ[X]
  | 0 => 2
  | n + 1 =>
      (C 1 * X + C (-1) * X ^ 3) * (A059427 n).derivative +
        (C 1 + C 2 * X + C (n : ℝ) * X ^ 2) * A059427 n

/-- The recurrence defining the A101280 row polynomials. -/
def A101280 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 1 * X + C (-4) * X ^ 2) * (A101280 n).derivative +
        (C 1 + C (2 * (n : ℝ)) * X) * A101280 n

/-- The recurrence defining the A101343 row polynomials. -/
def A101343 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C (-2) * X + C (-2) * X ^ 2) * (A101343 n).derivative +
        (C (1 + (n : ℝ)) + C (1 + (n : ℝ)) * X) * A101343 n

/-- The recurrence defining the A108426 row polynomials. -/
def A108426 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      let d : ℝ := -5 + -3 * (n : ℝ) + 2 * (2 + (n : ℝ)) ^ 2
      (C ((1 / d) * (-3 + (-9 / 2) * (n : ℝ))) * X +
          C ((1 / d) * (-3 + -5 * (n : ℝ))) * X ^ 2 +
          C ((-1 / 2) * (n : ℝ) * (1 / d)) * X ^ 3) *
          (A108426 n).derivative +
        (C ((1 / d) *
              (-51 + (-81 / 2) * (n : ℝ) + (27 / 2) * (2 + (n : ℝ)) ^ 2)) +
            C ((1 / d) *
              (-45 + 12 * (2 + (n : ℝ)) ^ 2 + (-71 / 2) * (n : ℝ))) * X +
            C ((1 / d) *
              (-2 + (1 / 2) * (2 + (n : ℝ)) ^ 2 + -2 * (n : ℝ))) * X ^ 2) *
          A108426 n

/-- The recurrence defining the A186370 row polynomials. -/
def A186370 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 1 * X + C (-1) * X ^ 3) * (A186370 n).derivative +
        (C 1 + C 1 * X + C (n : ℝ) * X ^ 2) * A186370 n

example (n : ℕ) : (A008303 n).natDegree = n / 2 := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (A008971 n).natDegree = n / 2 := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (A059427 n).natDegree = n := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (A101280 n).natDegree = n / 2 := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (A101343 n).natDegree = (n + 1) / 2 := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (A108426 n).natDegree = n := by
  rr_row_natDegree (via := cancel)

example (n : ℕ) : (A186370 n).natDegree = n := by
  rr_row_natDegree (via := cancel)

end

end RealRooted.Tactic.RowCancelRho
