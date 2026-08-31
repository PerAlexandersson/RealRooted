import RealRooted.Tactic.MaWang.Basic

/-!
# Ma--Wang tactic step syntax

Parser declarations for one-step Ma--Wang and weak derivative certificates.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_ma_wang)
  "rr_ma_wang" " using " term ", " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_inferred) "rr_ma_wang" : tactic

syntax (name := rr_ma_wang_named)
  "rr_ma_wang" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_same)
  "rr_ma_wang_same" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_same_inferred) "rr_ma_wang_same" : tactic

syntax (name := rr_ma_wang_same_named)
  "rr_ma_wang_same" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_succ)
  "rr_ma_wang_succ" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_succ_inferred) "rr_ma_wang_succ" : tactic

syntax (name := rr_ma_wang_succ_named)
  "rr_ma_wang_succ" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_prec_evalCoeff_nonpos_named)
  "rr_prec_evalCoeff_nonpos" " using "
    "interlaces" ":=" term ","
    "source_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_prec_evalCoeff_nonpos_degree_named)
  "rr_prec_evalCoeff_nonpos" " using "
    "interlaces" ":=" term ","
    "source_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_prec_evalCoeff_nonpos_inferred)
  "rr_prec_evalCoeff_nonpos" : tactic

syntax (name := rr_prec_evalCoeff_nonpos_degree_inferred)
  "rr_prec_evalCoeff_nonpos" " using " "degree" ":=" term : tactic

syntax (name := rr_mw_derivative_nonpos)
  "rr_mw_derivative_nonpos" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term :
  tactic

syntax (name := rr_mw_derivative_nonpos_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_step_named)
  "rr_mw_derivative_nonpos_step" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_step_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_step" " using " "recurrence" ":=" term : tactic

syntax (name := rr_mw_derivative_nonpos_degree_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_nonpos_inferred)
  "rr_mw_derivative_nonpos" : tactic

syntax (name := rr_mw_derivative_nonpos_degree_inferred)
  "rr_mw_derivative_nonpos" " using " "degree" ":=" term : tactic

syntax (name := rr_mw_derivative_sign_roots_nonpos_named)
  "rr_mw_derivative_sign_roots_nonpos" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_nonneg_coeffs_named)
  "rr_mw_derivative_sign_nonneg_coeffs" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_nonneg_factor_named)
  "rr_mw_derivative_sign_nonneg_factor" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_root_upper_named)
  "rr_mw_derivative_sign_root_upper" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_sign_window_named)
  "rr_mw_derivative_sign_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_mul_named)
  "rr_mw_derivative_X_mul" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_C_mul_X_mul_named)
  "rr_mw_derivative_C_mul_X_mul" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_X_one_add_window_named)
  "rr_mw_derivative_X_one_add_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_named)
  "rr_mw_derivative_neg_X_one_add_outer" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_one_add_outer_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_named)
  "rr_mw_derivative_one_add_two_window" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "degree_two" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_named)
  "rr_mw_derivative_neg_const" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_const_auto_named)
  "rr_mw_derivative_neg_const_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_named)
  "rr_mw_derivative_neg_X_sq" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_mw_derivative_neg_X_sq_auto_named)
  "rr_mw_derivative_neg_X_sq_auto" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

end Tactic
end RealRooted
