import RealRooted.Tactic.RowInterlacing

/-!
# Eigen-ODE examples

Regression tests for `rr_row_ode` and for `rr_row_interlaces` on second-order
recurrences `P (n + 1) = A * (P n)'' + B * (P n)' + C n * P n` of Laguerre type, drawn
from `real-rooted-oeis-proofs`.  `rr_find_ode` suggests the ODE statements used here.
-/

open Polynomial

namespace RealRooted.Tactic.RecurrenceODEExamples

noncomputable section

/-- Generalized Laguerre rows (A105278). -/
def A105278 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * (A105278 n).derivative.derivative + (2 + 2 * X) * (A105278 n).derivative +
      (2 + X) * A105278 n

theorem A105278_ode (n : ℕ) :
    X * (A105278 n).derivative.derivative + (2 + X) * (A105278 n).derivative =
      C (n : ℝ) * A105278 n := by
  rr_row_ode

theorem A105278_interlaces (n : ℕ) :
    RealRooted.Interlaces (A105278 n) (A105278 (n + 1)) := by
  rr_row_interlaces

/-- An ODE with a rational coefficient, and a recurrence written with `1 / 2` (A331333). -/
def A331333 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ((1 / 2) * X) * (A331333 n).derivative.derivative +
      ((1 / 2) + 2 * X) * (A331333 n).derivative + (1 + 2 * X) * A331333 n

theorem A331333_natDegree (n : ℕ) : (A331333 n).natDegree = n := by rr_row_natDegree

theorem A331333_ode :
    ∀ n : ℕ, (C (1 / 2 : ℝ) * X) * (A331333 n).derivative.derivative +
      (C (1 / 2 : ℝ) + X) * (A331333 n).derivative = C (n : ℝ) * A331333 n := by
  rr_row_ode

theorem A331333_interlaces (n : ℕ) :
    RealRooted.Interlaces (A331333 n) (A331333 (n + 1)) := by
  rr_row_interlaces

end

end RealRooted.Tactic.RecurrenceODEExamples
