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
    slope_pos := by norm_num,
    index := n

example {A : Nat → ℝ[X]}
    (h0 : A 0 = C (1 : ℝ))
    (h1 : A 1 = C (2 : ℝ) + C 3 * X)
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) + C 7 * X) * A (n + 1))
    (n : Nat) :
    Interlaces (A n) (A (n + 1)) := by
  rr_linear_tail_sequence_interlaces using
    c_pos := by norm_num,
    a_nonneg := by norm_num,
    b_pos := by norm_num,
    u_pos := by norm_num,
    v_pos := by norm_num,
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
    c_pos := by norm_num,
    a_nonneg := by norm_num,
    b_pos := by norm_num,
    u_pos := by norm_num,
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
    c_pos := by norm_num,
    a_nonneg := by norm_num,
    b_pos := by norm_num,
    u_pos := by norm_num,
    v_pos := by norm_num,
    base0 := h0,
    base1 := h1,
    recurrence := hstep,
    index := n

end Tactic
end RealRooted
