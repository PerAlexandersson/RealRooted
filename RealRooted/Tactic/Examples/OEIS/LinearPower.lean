import RealRooted.Tactic.LinearPowerFamily
import RealRooted.Tactic.SideGoals

/-!
# OEIS linear-power regression examples

Regression examples for the OEIS linear-power and side-goal frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Linear-power interlacing exit exposed through the OEIS facade. -/
example (n : Nat) :
    Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
      ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_interlaces_linear_pow using
    const := 2,
    slope := 3,
    slope_pos := rr_side_pos_term,
    index := n

/-- Linear-power nonnegative-coefficient exit exposed through the OEIS facade. -/
example (n : Nat) :
    HasNonnegCoeffs ((C (2 : ℝ) + C 3 * X) ^ n) := by
  rr_hasNonnegCoeffs_linear_pow using
    a_nonneg := rr_side_nonneg_term,
    b_nonneg := rr_side_nonneg_term,
    index := n


end Tactic
end RealRooted
