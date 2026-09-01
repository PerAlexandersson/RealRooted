import RealRooted.Tactic.MaWang.SequenceSyntax

/-!
# Ma--Wang tactic scalar-denominator syntax

Parser declarations for normalized scalar-denominator recurrence certificates.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonpos_of_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_on_roots_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_on_roots" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_on_roots" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted_named)
  "rr_mw_derivative_nonpos_nonneg_sequence_on_roots_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonpos_on_roots" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_sequence_nonneg_named)
  "rr_mw_derivative_X_mul_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_mul_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_nonneg_named)
  "rr_mw_derivative_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_nonneg_degree_succ_named)
  "rr_mw_derivative_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_sequence_realrooted_nonneg_degree_succ_named)
  "rr_mw_derivative_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "factor_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_mul_sequence_den_coeff_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff" ":=" term ","
    "factor_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

end Tactic
end RealRooted
