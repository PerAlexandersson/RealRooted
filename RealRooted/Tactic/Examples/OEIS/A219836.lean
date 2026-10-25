module

public import RealRooted.Applications.OEIS.A219836
public import RealRooted.Tactic.RowInterlacing

/-!
# A219836 degree-model regression

The definition and theorem below are the literal downstream recurrence and natural-degree
statement.  The proof exercises the default registered-model route.
-/

@[expose] public section

open RealRooted
open Polynomial

noncomputable section

namespace HA219836

/-- The OEIS A219836 polynomial sequence, given by a literal recurrence with derivative terms. -/
def A219836 : ℕ → ℝ[X]
  | 0 => 0
  | 1 => X
  | n + 2 =>
      ((C (1) * X + C (-1) * X ^ 2)) * (A219836 (n + 1)).derivative
        + ((C (1) * X ^ 2 + C (-1) * X ^ 3)) * (A219836 n).derivative
        + ((C (1) + C ((1 + (n : ℝ))) * X)) * A219836 (n + 1)
        + ((C (1) * X + C ((1 + (n : ℝ))) * X ^ 2)) * A219836 n

theorem A219836_natDegree (n : ℕ) :
    (A219836 (n + 1)).natDegree = if n % 2 = 0 then n + 1 else n := by
  rr_row_natDegree

end HA219836
