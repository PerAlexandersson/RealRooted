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

example {n : Nat} : (n : ℝ) + 3 ≠ 0 := by
  rr_side_ne

example {n : Nat} : 1 + ((n + 2 : Nat) : ℝ) / 2 ≠ 0 := by
  rr_side_ne

example {n : Nat} : -(((n : ℝ) + 5) * ((n : ℝ) + 1) / 3) ≠ 0 := by
  rr_side_ne

example (p q : ℝ[X]) (n : Nat) :
    (p + q).coeff n = p.coeff n + q.coeff n := by
  rr_coeff

example (p : ℝ[X]) (n : Nat) :
    (X * p).coeff (n + 1) = p.coeff n := by
  rr_coeff

example (p : ℝ[X]) :
    (X * p).coeff 0 = 0 := by
  rr_coeff

example (p : ℝ[X]) (n : Nat) :
    p.derivative.coeff n = p.coeff (n + 1) * ((n : ℝ) + 1) := by
  rr_coeff

example (p : ℝ[X]) (a n : Nat) :
    (((a : ℝ[X]) * p).coeff n) = (a : ℝ) * p.coeff n := by
  rr_coeff

example :
    ((X * (X + C 2) : ℝ[X]).coeff 2) = 1 := by
  rr_coeff

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
