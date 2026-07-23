import RealRooted.Tactic.LinearPowerFamily

/-!
# Linear-power family tactic examples

Small OEIS-agnostic regression examples for the fixed linear-factor backend.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example (n : Nat) :
    Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
      ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_interlaces_linear_pow using
    const := 2,
    slope := 3,
    slope_pos := rr_side_pos_term,
    index := n

example {A : Nat → ℝ[X]}
    (h0 : A 0 = C (1 : ℝ))
    (h1 : A 1 = C (2 : ℝ) + C 3 * X)
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) + C 7 * X) * A (n + 1))
    (n : Nat) :
    Interlaces (A n) (A (n + 1)) := by
  rr_linear_tail_sequence_interlaces using
    c_pos := rr_side_pos_term,
    a_nonneg := rr_side_nonneg_term,
    b_pos := rr_side_pos_term,
    u_pos := rr_side_pos_term,
    v_pos := rr_side_pos_term,
    base0 := h0,
    base1 := h1,
    recurrence := hstep,
    index := n

example {A : Nat → ℝ[X]}
    (h0 : A 0 = C (1 : ℝ))
    (h1 : A 1 = C (2 : ℝ) + C 3 * X)
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) * X) * A (n + 1))
    (n : Nat) :
    Interlaces (A n) (A (n + 1)) := by
  rr_monomial_tail_sequence_interlaces using
    c_pos := rr_side_pos_term,
    a_nonneg := rr_side_nonneg_term,
    b_pos := rr_side_pos_term,
    u_pos := rr_side_pos_term,
    base0 := h0,
    base1 := h1,
    recurrence := hstep,
    index := n

example {A : Nat → ℝ[X]}
    (h0 : A 0 = C (1 : ℝ))
    (h1 : A 1 = C (2 : ℝ) + C 3 * X)
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) + C 7 * X) * A (n + 1))
    (n : Nat) :
    A n ≠ 0 ∧ (A n).Splits := by
  rr_linear_tail_sequence_realrooted using
    c_pos := rr_side_pos_term,
    a_nonneg := rr_side_nonneg_term,
    b_pos := rr_side_pos_term,
    u_pos := rr_side_pos_term,
    v_pos := rr_side_pos_term,
    base0 := h0,
    base1 := h1,
    recurrence := hstep,
    index := n

end Tactic
end RealRooted
