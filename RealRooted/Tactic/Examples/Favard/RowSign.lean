import RealRooted.Tactic.Favard

/-!
# `rr_favard` examples: row signs

Abstract smoke tests for the row-sign Favard frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Projection endpoint for the monic row-sign Favard wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (((n + 1 : Nat) : ℝ)) - X) * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_param_row_sign_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Row-sign affine Favard with a factored scalar denominator. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) -
            C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The factored row-sign denominator path also dispatches global
real-rootedness endpoints. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) -
            C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The row-sign denominator path also accepts the mixed `n.succ` and
`C d_n * C beta_{n+1}` spelling. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n) * C (n.succ : ℝ) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The row-sign distributed path accepts the reversed scalar order on a
pointwise interlacing endpoint. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (n.succ : ℝ) * C (d n) * P n) :
    StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The row-sign distributed path accepts `C (beta_{n+1} * d_n)` as the lag
coefficient. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C ((n.succ : ℝ) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_favard_affine_param_row_sign_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Monic row-sign denominator alias with a positive variable lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_param_row_sign_den_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit monic row-sign denominator alias with a supplied lag-positivity
certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    P n ≠ 0 := by
  rr_favard_param_row_sign_den using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Affine row-sign denominator alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit affine row-sign denominator unit-lag alias with a supplied
slope-positivity certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_row_sign_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    slope_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Monic row-sign denominator alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_den_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Row-sign affine Favard with a distributed scalar denominator and explicit
positivity certificates, tested on a pointwise real-rootedness endpoint. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {s α β : Nat → ℝ} {n : Nat}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_den using
    slope := s,
    alpha := α,
    beta := β,
    slope_pos := hs,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

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

/-- Automatic positivity for parameterized affine row-sign wrappers. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (2 : ℝ) * X - C ((0 : Nat) : ℝ)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) -
          C ((((n + 1 : Nat) : ℝ) + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_row_sign_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Unit-lag affine row-sign wrapper. -/
example {P : Nat → ℝ[X]} {s α : Nat → ℝ} {n : Nat}
    (hs : ∀ n : Nat, 0 < s n)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) - P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_row_sign_unit using
    slope := s,
    alpha := α,
    slope_pos := hs,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Monic parameterized row-sign wrapper with explicit positivity. -/
example {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) = -(X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_param_row_sign using
    alpha := α,
    beta := β,
    beta_pos := hβ,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Automatic positivity for monic parameterized row-sign wrappers. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (n.succ : ℝ) - X) * P (n + 1) - C ((n.succ : ℝ) + 1) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_row_sign_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
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
