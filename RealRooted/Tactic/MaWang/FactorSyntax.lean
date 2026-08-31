import RealRooted.Tactic.MaWang.DenominatorSyntax

/-!
# Ma--Wang tactic factor syntax

Parser declarations for specialized derivative-factor sequence certificates.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_nonneg_degree_succ_named)
  "rr_mw_derivative_X_one_add_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_X_one_add_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name :=
    rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_add_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto_degree_succ_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "roots_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto_named)
  "rr_mw_derivative_C_mul_X_one_sub_X_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_root_window_linear_facts) "rr_mw_root_window_linear_facts" : tactic

syntax (name := rr_mw_two_variants) "rr_mw_two_variants" term ", " term : tactic
syntax (name := rr_mw_three_variants) "rr_mw_three_variants" term ", " term ", " term : tactic

end Tactic
end RealRooted
