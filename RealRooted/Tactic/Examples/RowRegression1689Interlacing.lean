import RealRooted.Tactic.RowInterlacing

/-!
# Interlacing-search regression examples for PR #1689

These exact downstream recurrence shapes exercise the direct, Euler-step, and reversal
routes that must finish before the nonlinear fallback of `rr_row_eval_sign` is considered.
-/

open Polynomial

namespace RealRooted.Tactic.RowRegression1689InterlacingExamples

noncomputable section

def A008957 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C 1 * X ^ 3 * (A008957 n).derivative.derivative +
        C (-1 - 2 * (n : ℝ)) * X ^ 2 * (A008957 n).derivative +
        (C 1 + C (-3 + (2 + (n : ℝ)) ^ 2 - 2 * (n : ℝ)) * X) * A008957 n

example (n : ℕ) : (A008957 n).Splits := by
  rr_row_splits

def A036969 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X ^ 2 * (A036969 n).derivative.derivative +
        3 * X * (A036969 n).derivative + (1 + X) * A036969 n

example (n : ℕ) : (A036969 n).Splits := by
  rr_row_splits

def A059110 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 + X) * (A059110 n).derivative.derivative +
        (2 + 2 * X) * (A059110 n).derivative + (1 + X) * A059110 n

example (n : ℕ) : (A059110 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A059110 n) (A059110 (n + 1)) := by
  rr_row_interlaces

def A080248 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 / 2 * X ^ 2) * (A080248 n).derivative.derivative +
        2 * X * (A080248 n).derivative + (1 + X) * A080248 n

example (n : ℕ) : (A080248 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A080248 n) (A080248 (n + 1)) := by
  rr_row_interlaces

def A166960 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C 1 * X ^ 2 * (A166960 n).derivative.derivative +
        (C 3 * X + C (-1) * X ^ 2) * (A166960 n).derivative +
        (C 1 + C (1 + (n : ℝ)) * X) * A166960 n

example (n : ℕ) : (A166960 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A166960 n) (A166960 (n + 1)) := by
  rr_row_interlaces

def A166961 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C 2 * X ^ 2 * (A166961 n).derivative.derivative +
        (C 5 * X + C (-2) * X ^ 2) * (A166961 n).derivative +
        (C 1 + C (1 + 2 * (n : ℝ)) * X) * A166961 n

example (n : ℕ) : (A166961 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A166961 n) (A166961 (n + 1)) := by
  rr_row_interlaces

def A166972 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C 3 * X ^ 2 * (A166972 n).derivative.derivative +
        (C 7 * X + C (-1) * X ^ 2) * (A166972 n).derivative +
        (C 1 + C (1 + (n : ℝ)) * X) * A166972 n

example (n : ℕ) : (A166972 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A166972 n) (A166972 (n + 1)) := by
  rr_row_interlaces

def A176230 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      4 * X * (A176230 n).derivative.derivative +
        (2 + 4 * X) * (A176230 n).derivative + (1 + X) * A176230 n

example (n : ℕ) : (A176230 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A176230 n) (A176230 (n + 1)) := by
  rr_row_interlaces

def A271703 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X * (A271703 n).derivative.derivative +
        2 * X * (A271703 n).derivative + X * A271703 n

example (n : ℕ) : (A271703 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (A271703 n) (A271703 (n + 1)) := by
  rr_row_interlaces

end
end RealRooted.Tactic.RowRegression1689InterlacingExamples
