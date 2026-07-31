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

example :
    ∀ n : Nat,
      Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
        ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_linear_power_sequence_interlaces using
    closed := by intro n; rfl,
    exponent_step := by intro n; rfl,
    slope_pos := rr_side_pos_term

example (n : Nat) :
    (C (2 : ℝ) + C 3 * X) ^ n ≠ 0 ∧
      ((C (2 : ℝ) + C 3 * X) ^ n).Splits := by
  rr_linear_power_sequence_realrooted using
    closed := by intro n; rfl,
    exponent_step := by intro n; rfl,
    slope_pos := rr_side_pos_term

example :
    ∀ n : Nat,
      Interlaces
        (C (((n + 1 : Nat) : ℝ)) * (C (2 : ℝ) + C 3 * X) ^ n)
        (C (((n + 2 : Nat) : ℝ)) * (C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_linear_power_scalar_sequence_interlaces using
    closed := by intro n; rfl,
    scalar_ne_zero := by
      intro n
      positivity,
    exponent_step := by intro n; rfl,
    slope_pos := rr_side_pos_term

example {P : Nat → ℝ[X]}
    (hclosed :
      ∀ n : Nat, ∃ c : ℝ,
        c ≠ 0 ∧ P n = C c * (C (2 : ℝ) + C 3 * X) ^ n)
    (n : Nat) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_linear_power_exists_scalar_sequence_realrooted using
    closed := hclosed,
    exponent_step := by intro n; rfl,
    slope_pos := rr_side_pos_term

example :
    ∀ n : Nat,
      Interlaces
        ((X - C (1 : ℝ)) ^ 2 * (C (2 : ℝ) + C 3 * X) ^ n)
        ((X - C (1 : ℝ)) ^ 2 * (C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_fixed_linear_power_sequence_interlaces using
    closed := by intro n; rfl,
    exponent_step := by intro n; rfl,
    slope_pos := rr_side_pos_term

example {P : Nat → ℝ[X]}
    (hclosed :
      ∀ n : Nat, P n = (X - C (1 : ℝ)) ^ 2 * (C (2 : ℝ) + C 3 * X) ^ n)
    (n : Nat) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_common_factor_linear_power_sequence_realrooted using
    fixed_realrooted := (show
      (X - C (1 : ℝ)) ^ 2 ≠ 0 ∧ ((X - C (1 : ℝ)) ^ 2).Splits by
      constructor
      · exact pow_ne_zero _ (X_sub_C_ne_zero (1 : ℝ))
      · exact (Polynomial.Splits.X_sub_C (1 : ℝ)).pow 2),
    closed := hclosed,
    exponent_step := by intro n; rfl,
    slope_pos := rr_side_pos_term

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
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) + C 7 * X) * A (n + 1)) :
    ∀ n : Nat, Interlaces (A n) (A (n + 1)) := by
  rr_linear_tail_sequence_interlaces using
    constant := 1,
    linear_const := 2,
    linear_slope := 3,
    tail_const := 5,
    tail_slope := 7,
    constant_pos := rr_side_pos_term,
    linear_const_nonneg := rr_side_nonneg_term,
    linear_slope_pos := rr_side_pos_term,
    tail_const_pos := rr_side_pos_term,
    tail_slope_pos := rr_side_pos_term,
    base0 := h0,
    base1 := h1,
    step := hstep

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
    (hstep : ∀ n, A (n + 2) = (C (5 : ℝ) * X) * A (n + 1))
    (n : Nat) :
    A n ≠ 0 ∧ (A n).Splits := by
  rr_monomial_tail_sequence_realrooted using
    constant := 1,
    linear_const := 2,
    linear_slope := 3,
    tail_slope := 5,
    constant_pos := rr_side_pos_term,
    linear_const_nonneg := rr_side_nonneg_term,
    linear_slope_pos := rr_side_pos_term,
    tail_slope_pos := rr_side_pos_term,
    base0 := h0,
    base1 := h1,
    step := hstep

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
