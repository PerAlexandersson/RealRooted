import RealRooted.Favard.Affine
import RealRooted.Tactic.Finish
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.SideGoals

open Polynomial

/-!
# Favard tactic

The tactic

```lean
rr_favard
rr_favard using hrec, hbeta
rr_favard_auto
```

applies the already-formalized Favard interface to goals that match
`favardInterlacing`,
`isRealRooted_of_favard`, or
`isGeneralizedSturmSeq_reverse_range_map_of_favard`.
The bare forms infer exact local recurrence and positivity hypotheses. Use an
explicit `using` form when more than one Favard certificate packet is in scope.
`rr_favard_affine_param_infer` keeps the coefficient families and recurrence
explicit while inferring positivity, base certificates, and the standard or
row-sign orientation.

First intended regression examples:

- Chebyshev-like examples;
- OEIS Family F examples after small wrapper definitions exist.
-/

namespace RealRooted

namespace Tactic

syntax (name := rr_favard_step_seq) "rr_favard_step_seq " term : term

syntax (name := rr_favard_step_dsimp_seq) "rr_favard_step_dsimp_seq " term : term

syntax (name := rr_favard_base_one) "rr_favard_base_one " term : term

syntax (name := rr_favard_base_one_dsimp) "rr_favard_base_one_dsimp " term : term

syntax (name := rr_favard_base_lookup_term) "rr_favard_base_lookup_term" : term

syntax (name := rr_favard_positive_lookup_term) "rr_favard_positive_lookup_term" : term

macro_rules
  | `(rr_favard_step_seq $hstep:term) =>
      `(fun n => by simpa using $hstep n)
  | `(rr_favard_step_dsimp_seq $hstep:term) =>
      `(by
        intro n
        first | dsimp | skip
        first
        | simpa using $hstep n
        | (convert ($hstep n) <;>
            first
              | (dsimp; simp; ring_nf)
              | (dsimp; simp)
              | (simp; ring_nf)
              | simp))
  | `(rr_favard_base_one $hP1:term) =>
      `(by simpa using $hP1)
  | `(rr_favard_base_one_dsimp $hP1:term) =>
      `(by
        first | dsimp | skip
        first
        | simpa using $hP1
        | (convert ($hP1) <;>
            first
              | (dsimp; simp; ring_nf)
              | (dsimp; simp)
              | (simp; ring_nf)
              | simp))
  | `(rr_favard_base_lookup_term) =>
      `(by
        first
          | rr_lookup
          | ((first | dsimp | skip); (first | simp | skip); rr_lookup))
  | `(rr_favard_positive_lookup_term) =>
      `(by
        first
          | rr_lookup
          | rr_positivity_seq)
syntax (name := rr_favard) "rr_favard" " using " term ", " term : tactic

syntax (name := rr_favard_inferred) "rr_favard" : tactic

syntax (name := rr_favard_named)
  "rr_favard" " using "
    "recurrence" ":=" term ","
    "beta_pos" ":=" term :
  tactic

syntax (name := rr_favard_auto_named)
  "rr_favard_auto" " using "
    "recurrence" ":=" term :
  tactic

syntax (name := rr_favard_auto_inferred) "rr_favard_auto" : tactic

syntax (name := rr_favard_const)
  "rr_favard_const" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_const_named)
  "rr_favard_const" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_auto_named)
  "rr_favard_const_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_unit_named)
  "rr_favard_const_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_unit)
  "rr_favard_const_unit" " using " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_param)
  "rr_favard_param" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_param_named)
  "rr_favard_param" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_auto_named)
  "rr_favard_param_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_unit_named)
  "rr_favard_param_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_unit)
  "rr_favard_param_unit" " using " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_const)
  "rr_favard_affine_const" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_const_named)
  "rr_favard_affine_const" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_auto_named)
  "rr_favard_affine_const_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_unit_named)
  "rr_favard_affine_const_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_unit)
  "rr_favard_affine_const_unit" " using " term ", " term ", " term ", "
    term ", " term :
  tactic

syntax (name := rr_favard_affine_const_row_sign_named)
  "rr_favard_affine_const_row_sign" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_row_sign_auto_named)
  "rr_favard_affine_const_row_sign_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_row_sign_unit_named)
  "rr_favard_const_row_sign_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_row_sign_unit)
  "rr_favard_const_row_sign_unit" " using " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_param)
  "rr_favard_affine_param" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_param_named)
  "rr_favard_affine_param" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_auto_named)
  "rr_favard_affine_param_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_infer_named)
  "rr_favard_affine_param_infer" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "step" ":=" term :
  tactic

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

syntax (name := rr_favard_param_den_unit_named)
  "rr_favard_param_den_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_unit_explicit_named)
  "rr_favard_affine_param_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_unit_named)
  "rr_favard_affine_param_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

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

syntax (name := rr_favard_affine_param_row_sign_auto_named)
  "rr_favard_affine_param_row_sign_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_named)
  "rr_favard_affine_param_row_sign_den" " using "
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

syntax (name := rr_favard_affine_param_row_sign_den_auto_named)
  "rr_favard_affine_param_row_sign_den_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

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

syntax (name := rr_favard_affine_param_row_sign_den_unit_explicit_named)
  "rr_favard_affine_param_row_sign_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_unit_named)
  "rr_favard_affine_param_row_sign_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_named)
  "rr_favard_param_row_sign_den" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_auto_named)
  "rr_favard_param_row_sign_den_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_unit_named)
  "rr_favard_param_row_sign_den_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_unit_explicit_named)
  "rr_favard_affine_param_row_sign_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_unit_named)
  "rr_favard_affine_param_row_sign_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_unit_named)
  "rr_favard_param_row_sign_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_named)
  "rr_favard_param_row_sign" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_auto_named)
  "rr_favard_param_row_sign_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_den_raw) "rr_favard_den_raw" " using " term : tactic

syntax (name := rr_favard_den_raw_term) "rr_favard_den_raw_term " term : term

macro "rr_favard_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

macro "rr_favard_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

macro "rr_favard_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

syntax (name := rr_favard_active_den_all_term)
  "rr_favard_active_den_all_term" : term

syntax (name := rr_favard_coeff_at_term)
  "rr_favard_coeff_at_term " term : term

syntax (name := rr_favard_coeff_all_term)
  "rr_favard_coeff_all_term" : term

syntax (name := rr_favard_goal_variants)
  "rr_favard_goal_variants"
    term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variants_interlaces)
  "rr_favard_goal_variants"
    term ", " term ", " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variants_seq)
  "rr_favard_goal_variants" term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variant_alternatives3)
  "rr_favard_goal_variant_alternatives3"
    term ", " term ", " term "; "
    term ", " term ", " term "; "
    term ", " term ", " term :
  tactic

syntax (name := rr_favard_refine_positivity_seq)
  "rr_favard_refine_positivity_seq " term :
  tactic

syntax (name := rr_favard_exact_realrooted_positivity_seq)
  "rr_favard_exact_realrooted_positivity_seq " term :
  tactic

macro_rules
  | `(tactic| rr_favard) =>
      `(tactic|
        rr_favard using
          recurrence := (by assumption),
          beta_pos := (by assumption))
  | `(tactic| rr_favard_auto) =>
      `(tactic|
        rr_favard_auto using
          recurrence := (by assumption))
  | `(tactic| rr_favard_refine_positivity_seq $h:term) =>
      `(tactic| rr_refine_then $h with rr_positivity_seq)
  | `(tactic| rr_favard_exact_realrooted_positivity_seq $h:term) =>
      `(tactic| rr_exact_realrooted_refine_then $h with rr_positivity_seq)
  | `(tactic|
      rr_favard_goal_variants
        $hinterlace:term, $hrealrooted:term, $hnonzero:term,
        $hinterlace_proj:term, $hrealrooted_proj:term, $hnonzero_proj:term) =>
      `(tactic|
        first
          | exact $hinterlace
          | rr_exact_realrooted_sequence_or_projection $hrealrooted
          | exact $hnonzero
          | exact $hinterlace_proj
          | rr_exact_realrooted_sequence_or_projection $hrealrooted_proj
          | exact $hnonzero_proj)
  | `(tactic|
      rr_favard_goal_variants
        $hinterlaces:term, $hprec:term, $hrealrooted:term, $hnonzero:term,
        $hinterlaces_proj:term, $hprec_proj:term, $hrealrooted_proj:term,
        $hnonzero_proj:term) =>
      `(tactic|
        first
          | exact $hinterlaces
          | exact $hprec
          | rr_exact_realrooted_sequence_or_projection $hrealrooted
          | exact $hnonzero
          | exact $hinterlaces_proj
          | exact $hprec_proj
          | rr_exact_realrooted_sequence_or_projection $hrealrooted_proj
          | exact $hnonzero_proj)
  | `(tactic|
      rr_favard_goal_variants
        $hinterlace:term, $hrealrooted:term, $hnonzero:term) =>
      `(tactic|
        rr_favard_goal_variants
          $hinterlace, $hrealrooted, $hnonzero,
          ($hinterlace _), ($hrealrooted _), ($hnonzero _))
  | `(tactic|
      rr_favard_goal_variant_alternatives3
        $hinterlace1:term, $hrealrooted1:term, $hnonzero1:term;
        $hinterlace2:term, $hrealrooted2:term, $hnonzero2:term;
        $hinterlace3:term, $hrealrooted3:term, $hnonzero3:term) =>
      `(tactic|
        first
          | rr_first_exact $hinterlace1, $hinterlace2, $hinterlace3
          | rr_first_exact $hrealrooted1, $hrealrooted2, $hrealrooted3
          | rr_first_exact $hnonzero1, $hnonzero2, $hnonzero3
          | rr_first_exact ($hinterlace1 _), ($hinterlace2 _), ($hinterlace3 _)
          | rr_first_exact ($hrealrooted1 _), ($hrealrooted2 _), ($hrealrooted3 _)
          | rr_first_exact ($hnonzero1 _), ($hnonzero2 _), ($hnonzero3 _))
  | `(tactic| rr_favard_den_raw using $hraw:term) =>
      `(tactic|
        first
          | intro n
            simpa [Nat.succ_eq_add_one] using $hraw n
          | intro n
            simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm, add_left_comm,
              add_assoc, C_mul, mul_assoc]
              using $hraw n
          | intro n
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, C_mul,
              mul_assoc] using $hraw n)
  | `(rr_favard_den_raw_term $hraw:term) =>
      `(by rr_favard_den_raw using $hraw)
  | `(rr_favard_active_den_all_term) =>
      `(by rr_favard_active_den_all)
  | `(rr_favard_coeff_at_term $n:term) =>
      `(by rr_favard_coeff_at $n)
  | `(rr_favard_coeff_all_term) =>
      `(by rr_favard_coeff_all)
  | `(tactic| rr_favard using $hrec:term, $hbeta:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing $hrec $hbeta
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard $hrec $hbeta)
          | exact RealRooted.nonzero_of_favard $hrec $hbeta
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta
          | exact RealRooted.favardInterlacing $hrec $hbeta _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard $hrec $hbeta _)
          | exact RealRooted.nonzero_of_favard $hrec $hbeta _
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta _)
  | `(tactic|
      rr_favard using
        recurrence := $hrec:term,
        beta_pos := $hbeta:term) =>
      `(tactic|
        rr_favard using $hrec, $hbeta)
  | `(tactic|
      rr_favard_auto using
        recurrence := $hrec:term) =>
      `(tactic|
        first
          | rr_favard_refine_positivity_seq
              (RealRooted.favardInterlacing $hrec ?_)
          | rr_favard_exact_realrooted_positivity_seq
              (RealRooted.isRealRooted_of_favard $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.nonzero_of_favard $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
                $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.favardInterlacing $hrec ?_ _)
          | rr_favard_exact_realrooted_positivity_seq
              (RealRooted.isRealRooted_of_favard $hrec ?_ _)
          | rr_favard_refine_positivity_seq
              (RealRooted.nonzero_of_favard $hrec ?_ _)
          | rr_favard_refine_positivity_seq
              (RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
                $hrec ?_ _))
  | `(tactic|
      rr_favard_const using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_const using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const using $α, $β, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_const_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_const_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const_auto using
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_const_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_const_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_param using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param using $α, $β, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_param_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_param_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param_auto using
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_param_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_affine_const using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const using
          $s, $α, $β, $hs, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_affine_const_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_term,
          beta_pos := rr_positivity_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_auto using
          slope := $s,
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_affine_const_unit using
        $s:term, $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_unit using
          slope := $s,
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const_row_sign using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_affine_const_row_sign_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_row_sign using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_term,
          beta_pos := rr_positivity_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_const_row_sign_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_row_sign_auto using
          slope := 1,
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_const_row_sign_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_const_row_sign_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_param_infer using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        step := $hstep:term) =>
      `(tactic|
        first
          | rr_favard_affine_param using
              slope := $s,
              alpha := $α,
              beta := $β,
              slope_pos := rr_favard_positive_lookup_term,
              beta_pos := rr_favard_positive_lookup_term,
              base_zero := rr_favard_base_lookup_term,
              base_one := rr_favard_base_lookup_term,
              step := rr_favard_step_dsimp_seq $hstep
          | rr_favard_affine_param_row_sign using
              slope := $s,
              alpha := $α,
              beta := $β,
              slope_pos := rr_favard_positive_lookup_term,
              beta_pos := rr_favard_positive_lookup_term,
              base_zero := rr_favard_base_lookup_term,
              base_one := rr_favard_base_lookup_term,
              step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.interlaces_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.favardInterlacing_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.interlaces_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _),
          (RealRooted.favardInterlacing_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _),
          (RealRooted.nonzero_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _))
  | `(tactic|
      rr_favard_affine_param using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using $s, $α, $β, $hs, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_affine_param_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param_den using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variant_alternatives3
          (RealRooted.favardInterlacing_affine_param_coeff_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)))
  | `(tactic|
      rr_favard_affine_param_den_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.interlaces_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.favardInterlacing_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.interlaces_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _),
          (RealRooted.favardInterlacing_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _))
  | `(tactic|
      rr_favard_affine_param_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
  | `(tactic|
      rr_favard_affine_param_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_prod_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_unit using
          slope := $s,
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw_auto using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw_unit using
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_param_row_sign using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_affine_param_row_sign_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param_row_sign_den using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variant_alternatives3
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)))
  | `(tactic|
      rr_favard_affine_param_row_sign_den_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_unit using
          slope := $s,
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw_auto using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw_unit using
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param_row_sign_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_row_sign_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_row_sign using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_param_row_sign_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param_row_sign using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)

end Tactic
end RealRooted
