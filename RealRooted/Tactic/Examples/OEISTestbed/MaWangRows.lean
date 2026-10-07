import RealRooted.Tactic.RowInterlacing

/-!
# OEIS test-bed Ma--Wang rows

Full-row regressions for the Ma--Wang families of `MaWangSteps`, whose sign certificates are
exercised there in isolation.  Each row is defined by its recurrence
`P (n + 1) = A n * (P n)' + B n * P n` or `P (n + 2) = a n * P (n + 1) + b n * P n`, and
`rr_row_*` proves interlacing and real-rootedness.
-/

open Polynomial

namespace RealRooted.Tactic.MaWangRowExamples

noncomputable section

/-- Dirichlet-eta table: `v_n(t) = 2t(1 - t)` (A156919). -/
def A156919 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 2 * X + C (-2) * X ^ 2) * (A156919 n).derivative +
      (C 2 + C (2 * (n : ℝ) + 1) * X) * A156919 n

theorem A156919_interlaces (n : ℕ) : Interlaces (A156919 n) (A156919 (n + 1)) := by
  rr_row_interlaces

theorem A156919_splits (n : ℕ) : (A156919 n).Splits := by rr_row_splits

/-- Scaled Eulerian rows `3ⁿ A(n + 1, k + 1)`: `v_n(t) = 3t(1 - t)` (A257620). -/
def A257620 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 3 * X + C (-3) * X ^ 2) * (A257620 n).derivative +
      (C 3 + C (3 * (n : ℝ) + 3) * X) * A257620 n

theorem A257620_interlaces (n : ℕ) : Interlaces (A257620 n) (A257620 (n + 1)) := by
  rr_row_interlaces

theorem A257620_splits (n : ℕ) : (A257620 n).Splits := by rr_row_splits

/-- Permutations by big descents: `v_n(t) = t(1 - t)` (A120434). -/
def A120434 : ℕ → ℝ[X]
  | 0 => 2
  | n + 1 => (C 1 * X + C (-1) * X ^ 2) * (A120434 n).derivative +
      (C 2 + C ((n : ℝ) + 1) * X) * A120434 n

theorem A120434_interlaces (n : ℕ) : Interlaces (A120434 n) (A120434 (n + 1)) := by
  rr_row_interlaces

theorem A120434_splits (n : ℕ) : (A120434 n).Splits := by rr_row_splits

/-- Ward-type rows: `v_n(t) = t(1 + t)` (A112493). -/
def A112493 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C 1 * X ^ 2) * (A112493 n).derivative +
      (C 1 + C ((n : ℝ) + 1) * X) * A112493 n

theorem A112493_interlaces (n : ℕ) : Interlaces (A112493 n) (A112493 (n + 1)) := by
  rr_row_interlaces

theorem A112493_splits (n : ℕ) : (A112493 n).Splits := by rr_row_splits

/-- Fubini polynomials: `v_n(t) = t(1 + t)` (A131689). -/
def A131689 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C 1 * X ^ 2) * (A131689 n).derivative + (C 0 + C 1 * X) * A131689 n

theorem A131689_interlaces (n : ℕ) : Interlaces (A131689 n) (A131689 (n + 1)) := by
  rr_row_interlaces

theorem A131689_splits (n : ℕ) : (A131689 n).Splits := by rr_row_splits

/-- Distinguished-block set partitions: `v_n(t) = 1 + t` (A049020). -/
def A049020 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 + C 1 * X) * (A049020 n).derivative + (C 1 + C 1 * X) * A049020 n

theorem A049020_interlaces (n : ℕ) : Interlaces (A049020 n) (A049020 (n + 1)) := by
  rr_row_interlaces

theorem A049020_splits (n : ℕ) : (A049020 n).Splits := by rr_row_splits

/-- Scaled Bell rows `2ⁿ Bell(n, (t + 1) / 2)`: `v_n(t) = 2 + 2t` (A154602). -/
def A154602 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 2 + C 2 * X) * (A154602 n).derivative + (C 1 + C 1 * X) * A154602 n

theorem A154602_interlaces (n : ℕ) : Interlaces (A154602 n) (A154602 (n + 1)) := by
  rr_row_interlaces

theorem A154602_splits (n : ℕ) : (A154602 n).Splits := by rr_row_splits

/-- Unsigned Laguerre rows `n! Lₙ(-t)`: `v_n(t) = t` (A021009). -/
def A021009 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 0 + C 1 * X) * (A021009 n).derivative +
      (C ((n : ℝ) + 1) + C 1 * X) * A021009 n

theorem A021009_interlaces (n : ℕ) : Interlaces (A021009 n) (A021009 (n + 1)) := by
  rr_row_interlaces

theorem A021009_splits (n : ℕ) : (A021009 n).Splits := by rr_row_splits

/-- Even binomial rows `∑ₖ C(2n, 2k) tᵏ`: lag `-(1 - t)²` (A086645). -/
def A086645 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (2 + 2 * X) * A086645 (n + 1) + (-1 + 2 * X + -1 * X ^ 2) * A086645 n

theorem A086645_interlaces (n : ℕ) : Interlaces (A086645 n) (A086645 (n + 1)) := by
  rr_row_interlaces

theorem A086645_splits (n : ℕ) : (A086645 n).Splits := by rr_row_splits

/-- Half the odd entries of even Pascal rows: lag `-(1 - t)²` (A091044). -/
def A091044 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | n + 2 => (2 + 2 * X) * A091044 (n + 1) + (-1 + 2 * X + -1 * X ^ 2) * A091044 n

theorem A091044_interlaces (n : ℕ) : Interlaces (A091044 n) (A091044 (n + 1)) := by
  rr_row_interlaces

theorem A091044_splits (n : ℕ) : (A091044 n).Splits := by rr_row_splits

end

end RealRooted.Tactic.MaWangRowExamples
