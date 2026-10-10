import RealRooted.Tactic.Favard

/-!
# `rr_favard` examples: denominator

Abstract smoke tests for the denominator-normalized Favard frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Positive-slope parameterized affine Favard unit-lag shape:
`P_{n+2}=(s_{n+1}t-α_{n+1})P_{n+1}-P_n`. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Projection endpoint for the affine parameterized Favard wrapper. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, (P n).Splits := by
  rr_favard_affine_param_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- The affine parameterized unit-lag wrapper also accepts an explicit
positive-slope certificate when the slope sequence is symbolic. -/
example {P : Nat → ℝ[X]} {s : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X)
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (((n + 1 : Nat) : ℝ))) * P (n + 1) - P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_unit using
    slope := s,
    alpha := fun m : Nat => (m : ℝ),
    slope_pos := hs,
    base_zero := hP0,
    base_one := hP1,
    step := hstep

/-- Positive-slope parameterized affine Favard smoke test with a scalar
denominator on the displayed recurrence. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n * (n.succ : ℝ)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The scalar-denominator affine Favard macro also handles distributed raw
recurrences on pointwise interlacing goals. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n * (n.succ : ℝ)) * P n) :
    StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The same distributed denominator path dispatches pointwise nonzero goals. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n * (n.succ : ℝ)) * P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Distributed raw recurrences may combine `n.succ` indexing with a lag
coefficient written as `C d_n * C beta_{n+1}`. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (d n) * C (n.succ : ℝ) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The distributed denominator path also accepts the reversed scalar order
`C beta_{n+1} * C d_n`. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C (n.succ : ℝ) * C (d n) * P n) :
    StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The lag coefficient may also be written as `C (beta_{n+1} * d_n)`. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1)) -
          C ((n.succ : ℝ) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- The scalar-denominator affine Favard macro also dispatches
real-rootedness endpoints with explicit positivity certificates. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den using
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

/-- The distributed denominator path also dispatches pointwise real-rootedness
endpoints with explicit positivity certificates. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {s α β : Nat → ℝ} {n : Nat}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den using
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

/-- Monic scalar-denominator Favard alias with automatic lag positivity. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_param_den_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit monic scalar-denominator Favard alias with a supplied lag
positivity certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((X - C (n.succ : ℝ)) * P (n + 1) -
          C (n.succ : ℝ) * P n)) :
    P n ≠ 0 := by
  rr_favard_param_den using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Affine scalar-denominator Favard alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Explicit affine scalar-denominator unit-lag alias with a supplied
slope-positivity certificate. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (2 : ℝ) * X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    slope_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Monic scalar-denominator Favard alias for unit lag. -/
example {P : Nat → ℝ[X]} {d : Nat → ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((X - C (n.succ : ℝ)) * P (n + 1) - P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_param_den_unit using
    alpha := fun m : Nat => (m : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := d,
    den_nonzero := hden,
    raw_recurrence := hraw

/-- Raw scalar-denominator Favard with product-displayed slope and lag
coefficients. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * C ((n : ℝ) + 2) * X + C (-((n : ℝ) + 1))) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_prod_auto using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => -((n : ℝ) + 1),
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Monic raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (1 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_param_den_raw_auto using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (1 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Monic unit-lag raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (1 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    P n ≠ 0 := by
  rr_favard_param_den_raw_unit using
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (1 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-((n : ℝ) + 2)) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -((n : ℝ) + 2),
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Automatic positivity variant of the affine raw scalar-denominator alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-((n : ℝ) + 2)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -((n : ℝ) + 2),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- The raw scalar-denominator router also exposes consecutive interlacing. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-((n : ℝ) + 2)) * P n) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_auto using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -((n : ℝ) + 2),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit product-displayed affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * C ((n : ℝ) + 2) * X + C (-((n : ℝ) + 1))) *
            P (n + 1) +
          C (-1 : ℝ) * C ((n : ℝ) + 2) * P n) :
    P n ≠ 0 := by
  rr_favard_affine_param_den_raw_prod using
    slope := fun m : Nat => 2 * ((m : ℝ) + 1),
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ) + 1,
    raw_slope_left := fun _ : Nat => (2 : ℝ),
    raw_slope_right := fun n : Nat => (n : ℝ) + 2,
    raw_const := fun n : Nat => -((n : ℝ) + 1),
    raw_lag_left := fun _ : Nat => (-1 : ℝ),
    raw_lag_right := fun n : Nat => (n : ℝ) + 2,
    slope_pos := rr_positivity_seq_term,
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one_dsimp hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Unit-lag affine raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (2 : ℝ) * X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (2 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-1 : ℝ) * P n) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_favard_affine_param_den_raw_unit using
    slope := fun _ : Nat => (2 : ℝ),
    alpha := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (2 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun _ : Nat => (-1 : ℝ),
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

/-- Explicit monic raw scalar-denominator Favard alias. -/
example {P : Nat → ℝ[X]} {n : Nat}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X)
    (hraw : ∀ n : Nat,
      C (1 : ℝ) * P (n + 2) =
        (C (1 : ℝ) * X + C (-(n.succ : ℝ))) * P (n + 1) +
          C (-(n.succ : ℝ)) * P n) :
    P n ≠ 0 := by
  rr_favard_param_den_raw using
    alpha := fun m : Nat => (m : ℝ),
    beta := fun m : Nat => (m : ℝ),
    raw_slope := fun _ : Nat => (1 : ℝ),
    raw_const := fun n : Nat => -(n.succ : ℝ),
    raw_lag := fun n : Nat => -(n.succ : ℝ),
    beta_pos := rr_positivity_seq_term,
    base_zero := hP0,
    base_one := rr_favard_base_one hP1,
    den := fun _ : Nat => (1 : ℝ),
    raw_recurrence := hraw

end Tactic
end RealRooted
