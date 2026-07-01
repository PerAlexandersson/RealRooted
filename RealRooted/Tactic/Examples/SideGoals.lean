import RealRooted.Tactic.SideGoals

/-!
# `rr_side` examples

Small goals that exercise the first side-goal tactic.
-/

open Polynomial

namespace RealRooted
namespace Tactic

@[rr_recurrence] lemma rr_side_attr_smoke : True := by
  trivial

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rr_side

example (n : Nat) : n ≤ n + 1 := by
  rr_side

example (p q : ℝ[X]) (r : ℝ) :
    (p + q).eval r = p.eval r + q.eval r := by
  rr_side

example (x : ℝ) :
    ((X + C 1 : ℝ[X]).eval x) = x + 1 := by
  rr_side

end Tactic
end RealRooted

