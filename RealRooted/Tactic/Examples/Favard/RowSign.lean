import RealRooted.Tactic.Favard

/-!
# `rr_favard` examples: row signs

Abstract smoke tests for the row-sign Favard frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Row-sign affine Favard with an unfactored raw scalar-denominator numerator. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_raw_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-2 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Row-sign raw scalar-denominator Favard with product-displayed slope and
lag coefficients. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * C ((n : ℝ) + 2) * X + C ((n : ℝ) + 1)) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den_raw_prod_auto using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (-2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => (n : ℝ) + 1,
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Row-sign monic raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-1 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_den_raw_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-1 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Row-sign monic unit-lag raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-1 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_den_raw_unit using
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-1 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Parameterized affine row-sign wrapper with explicit positivity
certificates. -/
example {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Explicit row-sign affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_raw using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-2 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit product-displayed row-sign affine raw denominator alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * C ((n : ℝ) + 2) * X + C ((n : ℝ) + 1)) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_row_sign_den_raw_prod using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (-2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => (n : ℝ) + 1,
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Unit-lag row-sign affine raw denominator alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-2 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den_raw_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-2 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit monic row-sign raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (-1 : ℝ) * X + C (n.succ : ℝ)) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_den_raw using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (-1 : ℝ),
    raw_const := fun n : Nat => (n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

end Tactic
end RealRooted
