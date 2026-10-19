import RealRooted.Applications.OEIS.A318107
import RealRooted.Tactic.RowInterlacing

open Polynomial

noncomputable section

namespace HA318107

/-- The OEIS A318107 polynomial sequence, given by a literal recurrence with derivative terms. -/
def A318107 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 6 + X
  | n + 2 =>
      ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
          (-30 + (-18 * (n : ℝ))))) * X +
        C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
          ((-15 / 2) + ((-9 / 2) * (n : ℝ))))) * X ^ 2)) *
        (A318107 (n + 1)).derivative +
      ((C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
          (-183 + (-81 * (n : ℝ)) + (27 * ((3 + (n : ℝ))) ^ (2))))) +
        C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
          (-34 + (-15 * (n : ℝ)) + (5 * ((3 + (n : ℝ))) ^ (2))))) * X)) *
        A318107 (n + 1) +
      (C (((1 / ((-5 + ((3 + (n : ℝ))) ^ (2) + (-2 * (n : ℝ))))) *
        (-4 + ((1 / 2) * ((3 + (n : ℝ))) ^ (2)) + (-2 * (n : ℝ))))) * X ^ 2) *
        A318107 n

theorem A318107_splits (n : ℕ) : (A318107 n).Splits := by
  rr_row_splits

theorem A318107_interlaces (n : ℕ) :
    RealRooted.Interlaces (A318107 n) (A318107 (n + 1)) := by
  rr_row_interlaces

theorem A318107_natDegree (n : ℕ) : (A318107 n).natDegree = n := by
  rr_row_natDegree

end HA318107
