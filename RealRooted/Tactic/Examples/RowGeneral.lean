import RealRooted.Tactic.RowInterlacing

/-!
# General recurrences and half growth

Regression tests for the fallback of the degree tactics to general linear recurrences
(`RealRooted.LinRec`: any order, mixed derivatives, top coefficients of either sign) and
for half-growth splitting in `rr_row_splits`
(`RealRooted.threeTermHalf_ne_zero_and_splits`), on OEIS rows drawn from
`real-rooted-oeis-proofs`.
-/

open Polynomial

namespace RealRooted.Tactic.RowGeneralExamples

noncomputable section

/-- An order-three recurrence whose top coefficients satisfy `c = c - 3 c + 3 c`
(A030524). -/
def A030524 : ℕ → ℝ[X]
  | 0 => 30 + 12 * X + X ^ 2
  | 1 => 135 + 96 * X + 18 * X ^ 2 + X ^ 3
  | 2 => 567 + 630 * X + 198 * X ^ 2 + 24 * X ^ 3 + X ^ 4
  | n + 3 => (9 + X) * A030524 (n + 2) + (-27 + -3 * X) * A030524 (n + 1) +
      (27 + 3 * X) * A030524 n

theorem A030524_natDegree (n : ℕ) : (A030524 n).natDegree = n + 2 := by rr_row_natDegree

/-- A second-order recurrence with derivatives of both earlier rows (A307419). -/
def A307419 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (C 1 * X) * (A307419 (n + 1)).derivative +
      (C (-1 + -1 * (n : ℝ)) * X) * (A307419 n).derivative +
      (C (2 + 2 * (n : ℝ)) + C 1 * X) * A307419 (n + 1) +
      C (9 + -1 * (3 + (n : ℝ)) ^ 2 + 5 * (n : ℝ)) * A307419 n

theorem A307419_natDegree (n : ℕ) : (A307419 n).natDegree = n := by rr_row_natDegree

/-- Half growth with a lag `X - 1` of constant sign product (A034839). -/
def A034839 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * A034839 (n + 1) + (-1 + X) * A034839 n

theorem A034839_splits (n : ℕ) : (A034839 n).Splits := by rr_row_splits

/-- Half growth with `n`-dependent coefficients (A008306). -/
def A008306 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2
  | n + 2 => C (3 + (n : ℝ)) * A008306 (n + 1) + (C (3 + (n : ℝ)) * X) * A008306 n

theorem A008306_splits (n : ℕ) : (A008306 n).Splits := by rr_row_splits

end

end RealRooted.Tactic.RowGeneralExamples
