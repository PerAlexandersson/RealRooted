module

import RealRooted.Applications.OEIS.A304334
import RealRooted.Tactic.RowInterlacing

set_option linter.privateModule false

/-!
# A304334 row-model regression

The generated second-derivative recurrence is recognized through the
registered Euler-bidiagonal model after its forced factor `X` is removed.
-/

open Polynomial RealRooted

noncomputable section

namespace RealRooted.Tactic.Examples.OEIS.A304334

private def row : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      X ^ 2 * (row (n + 1)).derivative.derivative +
        (X + 4 * X ^ 2) * (row (n + 1)).derivative +
        2 * X * row (n + 1)

/-- The default row tactic uses the registered divided Euler-bidiagonal model. -/
example (n : ℕ) : Interlaces (row n) (row (n + 1)) := by
  rr_row_interlaces

/-- The same model exposes the splitting component of interlacing. -/
example (n : ℕ) : (row n).Splits := by
  rr_row_splits

/-- The downstream strict-interlacing statement follows from the registered route. -/
example (n : ℕ) : StrictInterl (row n) (row (n + 1)) := by
  exact (show Interlaces (row n) (row (n + 1)) by rr_row_interlaces).toStrictInterl

end RealRooted.Tactic.Examples.OEIS.A304334
