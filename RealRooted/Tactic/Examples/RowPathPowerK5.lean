module

public import RealRooted.Tactic.RowInterlacing

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.Tactic.Examples.RowPathPowerK5

/-- The direct `k = 5`, `p = 1`, `c = 0` path-power family. -/
def direct : ℕ → ℝ[X]
  | 0 | 1 | 2 | 3 | 4 => 1
  | n + 5 => direct (n + 4) + X * direct n

/-- The reflected `k = 5`, `p = 1`, `c = 0` path-power family. -/
def reflected : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => X ^ 2
  | 3 => X ^ 3
  | 4 => X ^ 4
  | n + 5 => X * reflected (n + 4) + X ^ 4 * reflected n

/-- The reflected family with one extra zero of padding. -/
def padded : ℕ → ℝ[X]
  | 0 => X
  | 1 => X ^ 2
  | 2 => X ^ 3
  | 3 => X ^ 4
  | 4 => X ^ 5
  | n + 5 => X * padded (n + 4) + X ^ 4 * padded n

example (n : ℕ) : (direct n).Splits := by
  rr_row_splits

example (n : ℕ) : (reflected n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (reflected n) (reflected (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (padded n).Splits := by
  rr_row_splits

example (n : ℕ) : RealRooted.Interlaces (padded n) (padded (n + 1)) := by
  rr_row_interlaces

end RealRooted.Tactic.Examples.RowPathPowerK5
