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

example {c : ℝ} (hc : 0 ≤ c) : 0 ≤ c := by
  rr_side_nonneg

example {n : Nat} (hn : 1 ≤ n) : 0 ≤ (n : ℝ) - 1 := by
  rr_side_nonneg

example {n : Nat} (hn : 2 ≤ n) : 0 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
  rr_side_nonneg

example {c : ℝ} (hc : 0 < c) : 0 < c := by
  rr_side_pos

example {n : Nat} : 0 < (n : ℝ) + 1 := by
  rr_side_pos

example {n : Nat} (hn : 2 ≤ n) : 0 < (n : ℝ) - 1 := by
  rr_side_pos

example {c : ℝ} (hc : c ≠ 0) : c ≠ 0 := by
  rr_side_ne

example {n : Nat} : (n : ℝ) + 1 ≠ 0 := by
  rr_side_ne

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
