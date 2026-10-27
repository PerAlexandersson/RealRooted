module

public import RealRooted.Tactic.Favard.DenominatorSyntax

/-!
# Favard tactic row-sign syntax

Parser declarations for row-sign-normalized affine Favard certificates.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes the Favard conclusion for `P`, namely `∀ n, StrictInterl (P n) (P (n + 1))`,
`∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal states, for the row-sign
recurrence `P (n + 2) = -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
C (β (n + 1)) * P n` with
`P 1 = -(C (s 0) * X - C (α 0))`. Arguments: `slope`, `alpha` and `beta` (all `ℕ → ℝ`),
`slope_pos : ∀ n, 0 < s n`, `beta_pos : ∀ n, 0 < β (n + 1)`, `base_zero : P 0 = 1`,
`base_one`, and `step`, the recurrence. -/
syntax (name := rr_favard_affine_param_row_sign_named)
  "rr_favard_affine_param_row_sign" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Handles a raw recurrence whose coefficients are not normalized:
`raw_recurrence : ∀ n, C (d n) * P (n + 2) =
(C (raw_slope n) * X + C (raw_const n)) * P (n + 1) + C (raw_lag n) * P n`.
The three coefficient equalities identify the normalized `s (n + 1)`, `α (n + 1)`, and
`β (n + 1)` with `-((d n)⁻¹ * raw_slope n)`, `(d n)⁻¹ * raw_const n`, and
`-((d n)⁻¹ * raw_lag n)`, respectively. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_named)
  "rr_favard_affine_param_row_sign_den_raw" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_affine_param_row_sign_den_raw` in which `den_nonzero` and the three
coefficient identities are not given: they are discharged automatically by
`rr_favard_active_den_all` and `rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_active_named)
  "rr_favard_affine_param_row_sign_den_raw" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_row_sign_den_raw` that proves `slope_pos` and `beta_pos` by
`rr_positivity_seq_term`; the other arguments are as for `rr_favard_affine_param_row_sign_den_raw`.
-/
syntax (name := rr_favard_affine_param_row_sign_den_raw_auto_named)
  "rr_favard_affine_param_row_sign_den_raw_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_affine_param_row_sign_den_raw_auto` in which `den_nonzero` and the three
coefficient identities are not given: they are discharged automatically by
`rr_favard_active_den_all` and `rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_auto_active_named)
  "rr_favard_affine_param_row_sign_den_raw_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_row_sign_den_raw` in which the raw slope and lag are products
of two scalar sequences: `raw_recurrence` has the product coefficients
`C (raw_slope_left n) * C (raw_slope_right n) * X + C (raw_const n)` and
`C (raw_lag_left n) * C (raw_lag_right n)`, and the coefficient identities use
`raw_slope_left n * raw_slope_right n` and `raw_lag_left n * raw_lag_right n`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_named)
  "rr_favard_affine_param_row_sign_den_raw_prod" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_affine_param_row_sign_den_raw_prod` in which `den_nonzero` and the three
coefficient identities are not given: they are discharged automatically by
`rr_favard_active_den_all` and `rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_active_named)
  "rr_favard_affine_param_row_sign_den_raw_prod" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_row_sign_den_raw_prod` that proves `slope_pos` and `beta_pos`
by `rr_positivity_seq_term`; the other arguments are as for
`rr_favard_affine_param_row_sign_den_raw_prod`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_auto_named)
  "rr_favard_affine_param_row_sign_den_raw_prod_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_affine_param_row_sign_den_raw_prod_auto` in which `den_nonzero` and the three
coefficient identities are not given: they are discharged automatically by
`rr_favard_active_den_all` and `rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_auto_active_named)
  "rr_favard_affine_param_row_sign_den_raw_prod_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_row_sign_den_raw` for `β n = 1` for every `n`: `beta` and
`beta_pos` are omitted, and `beta_pos` is proved by `rr_positivity_seq_term`; the other arguments,
including `slope_pos`, are as for `rr_favard_affine_param_row_sign_den_raw`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_unit_explicit_named)
  "rr_favard_affine_param_row_sign_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_row_sign_den_raw` for `β n = 1` for every `n` in which also
`slope_pos` is omitted: `slope_pos` and `beta_pos` are proved by `rr_positivity_seq_term`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_unit_named)
  "rr_favard_affine_param_row_sign_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_affine_param_row_sign_den_raw_unit` in which `den_nonzero` and the three
coefficient identities are not given: they are discharged automatically by
`rr_favard_active_den_all` and `rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_row_sign_den_raw_unit_active_named)
  "rr_favard_affine_param_row_sign_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_row_sign_den_raw` where the slope is the constant `s n = 1`,
so `slope` and `slope_pos` are omitted; the other arguments are as for
`rr_favard_affine_param_row_sign_den_raw`. -/
syntax (name := rr_favard_param_row_sign_den_raw_named)
  "rr_favard_param_row_sign_den_raw" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_param_row_sign_den_raw` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_param_row_sign_den_raw_active_named)
  "rr_favard_param_row_sign_den_raw" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_param_row_sign_den_raw` that proves `beta_pos` by
`rr_positivity_seq_term`; the other arguments are as for `rr_favard_param_row_sign_den_raw`. -/
syntax (name := rr_favard_param_row_sign_den_raw_auto_named)
  "rr_favard_param_row_sign_den_raw_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_param_row_sign_den_raw_auto` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_param_row_sign_den_raw_auto_active_named)
  "rr_favard_param_row_sign_den_raw_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_row_sign_den_raw` for the constant slope `s n = 1` and
`β n = 1`: `slope`, `slope_pos`, `beta` and `beta_pos` are omitted, and the positivity side goals
are proved automatically. -/
syntax (name := rr_favard_param_row_sign_den_raw_unit_named)
  "rr_favard_param_row_sign_den_raw_unit" " using "
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_param_row_sign_den_raw_unit` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_param_row_sign_den_raw_unit_active_named)
  "rr_favard_param_row_sign_den_raw_unit" " using "
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

end Tactic
end RealRooted
