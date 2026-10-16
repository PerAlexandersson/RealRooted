module

public import RealRooted.Tactic.RowInterlacing

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Tactic.Examples.RowPathPower

/-- A193636, copied from the downstream row recurrence. -/
def a193636 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | n + 3 => (1 + 3 * X) * a193636 (n + 2) + (-3 * X ^ 2) * a193636 (n + 1) +
      X ^ 3 * a193636 n

/-- A109955, copied from the downstream row recurrence. -/
def a109955 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | n + 3 => (3 + X) * a109955 (n + 2) + (-3) * a109955 (n + 1) + a109955 n

/-- A127893, copied from the downstream row recurrence. -/
def a127893 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 + X
  | 2 => 6 + 6 * X + X ^ 2
  | n + 3 => (3 + X) * a127893 (n + 2) + (-3) * a127893 (n + 1) + a127893 n

/-- A206294, copied from the downstream row recurrence. -/
def a206294 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 3 * X + X ^ 2
  | 3 => 6 * X + 6 * X ^ 2 + X ^ 3
  | n + 4 => (3 + X) * a206294 (n + 3) + (-3) * a206294 (n + 2) + a206294 (n + 1)

/-- A109960, copied from the downstream row recurrence. -/
def a109960 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | 3 => 1 + 15 * X + 9 * X ^ 2 + X ^ 3
  | n + 4 => (4 + X) * a109960 (n + 3) + (-6) * a109960 (n + 2) +
      4 * a109960 (n + 1) + (-1) * a109960 n

/-- A116088, copied from the downstream row recurrence. -/
def a116088 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 2 * X + X ^ 2
  | n + 3 => X * a116088 (n + 2) + 2 * X * a116088 (n + 1) + X * a116088 n

/-- A116089, copied from the downstream row recurrence. -/
def a116089 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 3 * X + X ^ 2
  | 3 => 3 * X + 6 * X ^ 2 + X ^ 3
  | n + 4 => C 1 * X * a116089 (n + 3) + C 3 * X * a116089 (n + 2) +
      C 3 * X * a116089 (n + 1) + C 1 * X * a116089 n

/-- A277627, copied from the downstream row recurrence. -/
def a277627 : ℕ → ℝ[X]
  | 0 => X
  | 1 => X ^ 2
  | 2 => X ^ 3
  | n + 3 => X * a277627 (n + 2) + X ^ 2 * a277627 n

example (n : ℕ) : (a193636 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a193636 n) (a193636 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a109955 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a109955 n) (a109955 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a127893 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a127893 n) (a127893 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a206294 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a206294 n) (a206294 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a109960 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a109960 n) (a109960 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a116088 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a116088 n) (a116088 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a116089 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a116089 n) (a116089 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a277627 n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (a277627 n) (a277627 (n + 1)) := by
  rr_row_interlaces

end RealRooted.Tactic.Examples.RowPathPower
