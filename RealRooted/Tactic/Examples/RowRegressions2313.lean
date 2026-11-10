module

public import RealRooted.Basic
import RealRooted.Tactic.Row.Frontend
import RealRooted.Tactic.Row.PathPower
import RealRooted.Tactic.Row.Subseq

/-!
# Lost row-route regressions

These downstream-shaped rows exercise coefficient nonnegativity inside the three-term and
first-order derivative interlacing routes.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.Examples.RowRegressions2313

noncomputable section

/-- A three-term row whose interlacing route needs nonnegative coefficients by induction. -/
def classTwoRows : ℕ → ℝ[X]
  | 0 => 2
  | 1 => 3 + 3 * X
  | 2 => 2 + 14 * X + 2 * X ^ 2
  | n + 3 => (1 + X) * classTwoRows (n + 2) + 3 * X * classTwoRows (n + 1)

/-- Consecutive rows of `classTwoRows` interlace by the plain row tactic. -/
theorem classTwoRows_interlaces (n : ℕ) :
    Interlaces (classTwoRows n) (classTwoRows (n + 1)) := by
  rr_row_interlaces

/-- A first-order derivative row with a rational quadratic derivative multiplier. -/
def classOneRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C ((1 / ((-1 / 2) * (n : ℝ) + (-1 / 2) * (2 + (n : ℝ)) ^ 2)) *
            (-5 / 2 + -1 * (n : ℝ))) * X +
          C ((1 / ((-1 / 2) * (n : ℝ) + (-1 / 2) * (2 + (n : ℝ)) ^ 2)) *
            (5 / 2 + (n : ℝ))) * X ^ 2) *
        (classOneRows n).derivative +
      (C 1 +
          C ((1 / ((-1 / 2) * (n : ℝ) + (-1 / 2) * (2 + (n : ℝ)) ^ 2)) *
            (-2 + (-3 / 2) * (2 + (n : ℝ)) ^ 2 + (-1 / 2) * (n : ℝ))) * X) *
        classOneRows n

/-- Consecutive rows of `classOneRows` interlace by the plain row tactic. -/
theorem classOneRows_interlaces (n : ℕ) :
    Interlaces (classOneRows n) (classOneRows (n + 1)) := by
  rr_row_interlaces

/-- A lag-two row with literal multipliers (A109446): the degree side goals of its residue
classes, such as `0 ≤ (2 + 2 * X).coeff 1`, need the general side-goal closer (#2366). -/
def residueRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1 + X
  | 3 => 3 + X
  | n + 4 => (2 + 2 * X) * residueRows (n + 2) + (-1 + -1 * X ^ 2 + 2 * X) * residueRows n

/-- The rows of `residueRows` split by the plain row tactic. -/
theorem residueRows_splits (n : ℕ) : (residueRows n).Splits := by
  rr_row_splits

/-- A cubic-parent row whose recurrence is not written in the canonical form (A184883). -/
def cubicParentRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | n + 3 => (1 + 2 * X) * cubicParentRows (n + 2) +
      (-1 * X ^ 2 + 2 * X) * cubicParentRows (n + 1) + X ^ 2 * cubicParentRows n

/-- The rows of `cubicParentRows` split by the plain row tactic. -/
theorem cubicParentRows_splits (n : ℕ) : (cubicParentRows n).Splits := by
  rr_row_splits

end
end RealRooted.Tactic.Examples.RowRegressions2313
