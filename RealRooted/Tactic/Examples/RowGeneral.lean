import RealRooted.Tactic.RowInterlacing

/-!
# General recurrences and half growth

Regression tests for the fallback of the degree tactics to general linear recurrences
(`RealRooted.LinRec`: any order, mixed derivatives, top coefficients of either sign) and
for half-growth splitting in `rr_row_splits`
(`RealRooted.threeTermHalf_ne_zero_and_splits`) and interlacing after a dropped row, on
OEIS rows drawn from `real-rooted-oeis-proofs`.
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

/-- The multiplier vanishes at `n = 0`: the first two rows are constant, and the rows
interlace from row `1` on (A055356). -/
def A055356 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X) * (A055356 n).derivative + (C 1 + C (n : ℝ) * X) * A055356 n

theorem A055356_interlaces (n : ℕ) : Interlaces (A055356 (n + 1)) (A055356 (n + 2)) := by
  rr_row_interlaces
theorem A055356_splits (n : ℕ) : (A055356 n).Splits := by rr_row_splits

/-- As above, with `A n = X - X ^ 2` changing sign (A163936). -/
def A163936 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C (-1) * X ^ 2) * (A163936 n).derivative +
      (C (1 + (n : ℝ)) + C (n : ℝ) * X) * A163936 n

theorem A163936_splits (n : ℕ) : (A163936 n).Splits := by rr_row_splits

/-- Two equal-degree rows dropped before linear growth: degree `n - 1` (A271697). -/
def A271697 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 => (C 1 * X + C (-1) * X ^ 2) * (A271697 (n + 1)).derivative +
      (C (1 + (n : ℝ)) * X) * A271697 (n + 1) + (C (1 + (n : ℝ)) * X) * A271697 n

theorem A271697_natDegree (n : ℕ) : (A271697 n).natDegree = n - 1 := by rr_row_natDegree

/-- A negative multiplier with Fibonacci top coefficients, by a ratio invariant (A046741). -/
def A046741 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + 2 * X ^ 2
  | n + 3 => (1 + 2 * X) * A046741 (n + 2) + X * A046741 (n + 1) + (-1 * X ^ 3) * A046741 n

theorem A046741_natDegree (n : ℕ) : (A046741 n).natDegree = n := by rr_row_natDegree
theorem A046741_leadingCoeff_pos (n : ℕ) : 0 < (A046741 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- Top coefficients `n + 1`, with derivatives of both earlier rows (A065826). -/
def A065826 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 => (C 1 * X + C (-1) * X ^ 2) * (A065826 (n + 1)).derivative +
      (C (-3 + -1 * (n : ℝ)) * X ^ 2 + C (3 + (n : ℝ)) * X ^ 3) * (A065826 n).derivative +
      (C 1 + C (4 + 2 * (n : ℝ)) * X) * A065826 (n + 1) +
      (C (6 + -1 * (3 + (n : ℝ)) ^ 2 + 2 * (n : ℝ)) * X ^ 2) * A065826 n

theorem A065826_natDegree (n : ℕ) : (A065826 n).natDegree = n := by rr_row_natDegree

end

end RealRooted.Tactic.RowGeneralExamples
