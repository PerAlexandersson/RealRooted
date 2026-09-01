import RealRooted.Tactic.Favard.DenominatorSyntax

/-!
# Favard tactic row-sign syntax

Parser declarations for row-sign-normalized affine Favard certificates.
-/

namespace RealRooted
namespace Tactic

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

end Tactic
end RealRooted
