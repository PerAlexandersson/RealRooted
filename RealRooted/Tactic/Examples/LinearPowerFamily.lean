import RealRooted.Tactic.LinearPowerFamily

/-!
# Linear-power family tactic examples

Small OEIS-agnostic regression examples for the fixed linear-factor backend.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (n : Nat) :
    Interlaces (C c * (X : ℝ[X]) ^ n) (C d * X ^ (n + 1)) := by
  rr_interlaces_C_mul_linear_pow_succ using
    left_scalar := c,
    right_scalar := d,
    const := 0,
    slope := 1,
    left_scalar_ne := hc,
    right_scalar_ne := hd,
    slope_pos := rr_side_pos_term,
    index := n

end Tactic
end RealRooted
