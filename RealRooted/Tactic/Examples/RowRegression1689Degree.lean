import RealRooted.Tactic.RowInterlacing

/-!
# Degree-pattern regression examples for PR #1689

These exact downstream recurrence shapes have degree `n / 2`.  Their splitting proofs use
the degree-pattern route while keeping the coefficient normalization needed by A263789.
-/

open Polynomial

namespace RealRooted.Tactic.RowRegression1689DegreeExamples

noncomputable section

def A008303 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 2 * X + C (-2) * X ^ 2) * (A008303 n).derivative +
        (C 2 + C (n : ℝ) * X) * A008303 n

example (n : ℕ) : (A008303 n).Splits := by
  rr_row_splits

def A008971 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 2 * X + C (-2) * X ^ 2) * (A008971 n).derivative +
        (C 1 + C (n : ℝ) * X) * A008971 n

example (n : ℕ) : (A008971 n).Splits := by
  rr_row_splits

def A094503 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 1 * X + C (-2) * X ^ 2) * (A094503 n).derivative +
        (C 1 + C (n : ℝ) * X) * A094503 n

example (n : ℕ) : (A094503 n).Splits := by
  rr_row_splits

def A101280 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 1 * X + C (-4) * X ^ 2) * (A101280 n).derivative +
        (C 1 + C (2 * (n : ℝ)) * X) * A101280 n

example (n : ℕ) : (A101280 n).Splits := by
  rr_row_splits

end
end RealRooted.Tactic.RowRegression1689DegreeExamples
