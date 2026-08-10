import RealRooted.Tactic.LinearPowerFamily

/-!
# Linear-power family tactic examples

Small OEIS-agnostic regression examples for the fixed linear-factor backend.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} (hgf : Prec g f)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) (n : Nat) :
    Prec (X ^ n * f) (X ^ (n + 1) * g) := by
  rr_prec_X_pow_mul_X_pow_succ using
    reverse_prec := hgf,
    left_nonneg := hfnn,
    right_nonneg := hgnn,
    index := n

example (n : Nat) :
    Interlaces ((C (2 : ℝ) + C 3 * X) ^ n)
      ((C (2 : ℝ) + C 3 * X) ^ (n + 1)) := by
  rr_interlaces_linear_pow using
    const := 2,
    slope := 3,
    slope_pos := rr_side_pos_term,
    index := n

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
