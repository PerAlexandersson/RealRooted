module

public import RealRooted.Tactic.Favard.DirectSyntax

/-!
# Favard tactic denominator syntax

Parser declarations for scalar-normalized and raw-affine Favard certificates.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Closes the Favard conclusion for `P`, namely `∀ n, StrictInterl (P n) (P (n + 1))`,
`∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal states, for the positive-slope
parameterized recurrence with a scalar denominator. Here `raw_recurrence` is the recurrence
`P (n + 2) = (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n` multiplied
through by `C (d n)` (also accepted with `d n` distributed over the two summands, in either scalar
order). Arguments: `slope`, `alpha` and `beta` (all `ℕ → ℝ`), `slope_pos : ∀ n, 0 < s n`,
`beta_pos : ∀ n, 0 < β (n + 1)`, `base_zero : P 0 = 1`, `base_one : P 1 = C (s 0) * X - C (α 0)`,
`den : ℕ → ℝ` (the scalars `d`), `den_nonzero : ∀ n, d n ≠ 0` and `raw_recurrence`. -/
syntax (name := rr_favard_affine_param_den_named)
  "rr_favard_affine_param_den" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_den` that proves `slope_pos` and `beta_pos` by
`rr_positivity_seq_term`; the other arguments are as for `rr_favard_affine_param_den`. -/
syntax (name := rr_favard_affine_param_den_auto_named)
  "rr_favard_affine_param_den_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Form of `rr_favard_affine_param_den_auto` in which `den_nonzero` is not given: it is discharged
automatically by `rr_favard_active_den_all`. -/
syntax (name := rr_favard_affine_param_den_auto_active_named)
  "rr_favard_affine_param_den_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Closes `∀ n, Interlaces (P n) (P (n + 1))` or the Favard conclusion for `P`, namely
`∀ n, StrictInterl (P n) (P (n + 1))`, `∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal
states, for a recurrence with a scalar denominator and raw, unnormalized coefficients:
`raw_recurrence`, in which `C (d n) * P (n + 2)` equals
`(C (raw_slope n) * X + C (raw_const n)) * P (n + 1) + C (raw_lag n) * P n`, and `slope_coeff_eq`,
`alpha_coeff_eq` and `beta_coeff_eq` identify the normalized `s (n + 1)`, `α (n + 1)` and
`β (n + 1)` with `(d n)⁻¹ * raw_slope n`, `-((d n)⁻¹ * raw_const n)` and `-((d n)⁻¹ * raw_lag n)`.
The other arguments are `slope`, `alpha`, `beta`, `raw_slope`, `raw_const`, `raw_lag`, `slope_pos`,
`beta_pos`, `base_zero`, `base_one`, `den` and `den_nonzero`, as for
`rr_favard_affine_param_den`. -/
syntax (name := rr_favard_affine_param_den_raw_named)
  "rr_favard_affine_param_den_raw" " using "
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

/-- Form of `rr_favard_affine_param_den_raw` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_den_raw_active_named)
  "rr_favard_affine_param_den_raw" " using "
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

/-- Version of `rr_favard_affine_param_den_raw` that proves `slope_pos` and `beta_pos` by
`rr_positivity_seq_term`; the other arguments are as for `rr_favard_affine_param_den_raw`. -/
syntax (name := rr_favard_affine_param_den_raw_auto_named)
  "rr_favard_affine_param_den_raw_auto" " using "
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

/-- Form of `rr_favard_affine_param_den_raw_auto` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_den_raw_auto_active_named)
  "rr_favard_affine_param_den_raw_auto" " using "
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

/-- Version of `rr_favard_affine_param_den_raw` whose raw slope and lag coefficients are products of
two sequences: `raw_slope_left` and `raw_slope_right` replace `raw_slope`, and `raw_lag_left` and
`raw_lag_right` replace `raw_lag`, so that `raw_recurrence` has `C (d n) * P (n + 2)` equal to
`(C (raw_slope_left n) * C (raw_slope_right n) * X + C (raw_const n)) * P (n + 1)` plus
`C (raw_lag_left n) * C (raw_lag_right n) * P n`, and the coefficient identities use the
products. -/
syntax (name := rr_favard_affine_param_den_raw_prod_named)
  "rr_favard_affine_param_den_raw_prod" " using "
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

/-- Form of `rr_favard_affine_param_den_raw_prod` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_den_raw_prod_active_named)
  "rr_favard_affine_param_den_raw_prod" " using "
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

/-- Version of `rr_favard_affine_param_den_raw_prod` that proves `slope_pos` and `beta_pos` by
`rr_positivity_seq_term`; the other arguments are as for `rr_favard_affine_param_den_raw_prod`. -/
syntax (name := rr_favard_affine_param_den_raw_prod_auto_named)
  "rr_favard_affine_param_den_raw_prod_auto" " using "
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

/-- Form of `rr_favard_affine_param_den_raw_prod_auto` in which `den_nonzero` and the three
coefficient identities are not given: they are discharged automatically by
`rr_favard_active_den_all` and `rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_den_raw_prod_auto_active_named)
  "rr_favard_affine_param_den_raw_prod_auto" " using "
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

/-- Version of `rr_favard_affine_param_den_raw` for `β n = 1` for every `n`: `beta` and `beta_pos`
are omitted and the positivity of `β` is proved by `rr_positivity_seq_term`, while `slope_pos` is
still given; the other arguments are as for `rr_favard_affine_param_den_raw`. -/
syntax (name := rr_favard_affine_param_den_raw_unit_explicit_named)
  "rr_favard_affine_param_den_raw_unit" " using "
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

/-- Version of `rr_favard_affine_param_den_raw_unit` without `slope_pos`, which is proved by
`rr_positivity_seq_term`; the other arguments are as there. -/
syntax (name := rr_favard_affine_param_den_raw_unit_named)
  "rr_favard_affine_param_den_raw_unit" " using "
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

/-- Form of `rr_favard_affine_param_den_raw_unit` without `slope_pos`, in which `den_nonzero` and
the three coefficient identities are not given: they are discharged automatically by
`rr_favard_active_den_all` and `rr_favard_coeff_all`. -/
syntax (name := rr_favard_affine_param_den_raw_unit_active_named)
  "rr_favard_affine_param_den_raw_unit" " using "
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

/-- Version of `rr_favard_affine_param_den_raw` for `s n = 1` for every `n`: `slope` and `slope_pos`
are omitted, and the other arguments are as for `rr_favard_affine_param_den_raw`. -/
syntax (name := rr_favard_param_den_raw_named)
  "rr_favard_param_den_raw" " using "
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

/-- Form of `rr_favard_param_den_raw` in which `den_nonzero` and the three coefficient identities
are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_param_den_raw_active_named)
  "rr_favard_param_den_raw" " using "
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

/-- Version of `rr_favard_param_den_raw` that proves `beta_pos` by `rr_positivity_seq_term`; the
other arguments are as for `rr_favard_param_den_raw`. -/
syntax (name := rr_favard_param_den_raw_auto_named)
  "rr_favard_param_den_raw_auto" " using "
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

/-- Form of `rr_favard_param_den_raw_auto` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_param_den_raw_auto_active_named)
  "rr_favard_param_den_raw_auto" " using "
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

/-- Version of `rr_favard_param_den_raw` for `β n = 1` for every `n`: `beta` and `beta_pos` are
omitted, and the positivity side conditions are proved by `rr_positivity_seq_term`; the other
arguments are as for `rr_favard_affine_param_den_raw_unit`. -/
syntax (name := rr_favard_param_den_raw_unit_named)
  "rr_favard_param_den_raw_unit" " using "
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

/-- Form of `rr_favard_param_den_raw_unit` in which `den_nonzero` and the three coefficient
identities are not given: they are discharged automatically by `rr_favard_active_den_all` and
`rr_favard_coeff_all`. -/
syntax (name := rr_favard_param_den_raw_unit_active_named)
  "rr_favard_param_den_raw_unit" " using "
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_den` for `β n = 1` for every `n`: `beta` and `beta_pos` are
omitted and the positivity of `β` is proved by `rr_positivity_seq_term`, while `slope_pos` is still
given; the other arguments are as for `rr_favard_affine_param_den`. -/
syntax (name := rr_favard_affine_param_den_unit_explicit_named)
  "rr_favard_affine_param_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_den_unit` without `slope_pos`, which is proved by
`rr_positivity_seq_term`; the other arguments are as there. -/
syntax (name := rr_favard_affine_param_den_unit_named)
  "rr_favard_affine_param_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_den` for `s n = 1` for every `n`: `slope` and `slope_pos` are
omitted, and the other arguments are as for `rr_favard_affine_param_den`. -/
syntax (name := rr_favard_param_den_named)
  "rr_favard_param_den" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_param_den` that proves `beta_pos` by `rr_positivity_seq_term`; the other
arguments are as for `rr_favard_param_den`. -/
syntax (name := rr_favard_param_den_auto_named)
  "rr_favard_param_den_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_param_den` for `β n = 1` for every `n`: `beta` and `beta_pos` are omitted,
and the positivity side conditions are proved by `rr_positivity_seq_term`; the other arguments are
as for `rr_favard_affine_param_den_unit`. -/
syntax (name := rr_favard_param_den_unit_named)
  "rr_favard_param_den_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param` for `β n = 1` for every `n`: `beta` and `beta_pos` are
omitted and positivity of `β` is proved by `rr_positivity_seq_term`, while `slope_pos` is still
given; the other arguments are `slope`, `alpha`, `base_zero`, `base_one` and `step`, as for
`rr_favard_affine_param`. -/
syntax (name := rr_favard_affine_param_unit_explicit_named)
  "rr_favard_affine_param_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param_unit` without `slope_pos`, which is proved by
`rr_positivity_seq_term`; the other arguments are as there. -/
syntax (name := rr_favard_affine_param_unit_named)
  "rr_favard_affine_param_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic


end Tactic
end RealRooted
