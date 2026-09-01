import RealRooted.Tactic.MaWang.StepSyntax

/-!
# Ma--Wang tactic sequence syntax

Parser declarations for ordinary derivative and derivative-plus-lag sequences.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_mw_derivative_nonpos_sequence_named)
  "rr_mw_derivative_nonpos_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_sequence" " using " "recurrence" ":=" term : tactic

syntax (name := rr_mw_derivative_nonpos_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_realrooted_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_sequence_realrooted" " using "
    "recurrence" ":=" term : tactic

syntax (name := rr_mw_derivative_global_nonpos_sequence_auto_named)
  "rr_mw_derivative_global_nonpos_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_global_nonpos_sequence_realrooted_auto_named)
  "rr_mw_derivative_global_nonpos_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_named)
  "rr_mw_derivative_neg_const_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_auto_named)
  "rr_mw_derivative_neg_const_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_named)
  "rr_mw_derivative_neg_const_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_const_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_named)
  "rr_mw_derivative_neg_X_sq_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_auto_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_sequence_realrooted_auto_degree_succ_named)
  "rr_mw_derivative_neg_X_sq_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_X_sequence_named)
  "rr_mw_derivative_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_one_add_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sub_one_sequence_named)
  "rr_mw_derivative_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_sub_one_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_named)
  "rr_mw_derivative_nonpos_nonneg_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_root_upper_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_root_upper_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_sign_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_realrooted_sign_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_window_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "deriv_coeff_eq" ":=" term ","
    "lag_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

syntax (name := rr_mw_lw_den_coeff_realrooted_window_scalar_named)
  "rr_mw_lw_derivative_lag_sequence_den_coeff_realrooted_window_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "lag_factor" ":=" term ","
    "norm_deriv_coeff" ":=" term ","
    "norm_lag_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_deriv_coeff" ":=" term ","
    "raw_lag_coeff" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

end Tactic
end RealRooted
