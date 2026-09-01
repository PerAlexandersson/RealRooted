import RealRooted.Tactic.WagnerX.TranslatedLag

/-!
# Wagner `X`-shift tactic syntax
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_prec_mul_X)
  "rr_prec_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

syntax (name := rr_prec_mul_X_inferred)
  "rr_prec_mul_X" : tactic

syntax (name := rr_prec_mul_X_both)
  "rr_prec_mul_X_both" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

syntax (name := rr_prec_mul_X_both_inferred)
  "rr_prec_mul_X_both" : tactic

syntax (name := rr_prec_C_mul_X)
  "rr_prec_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_ne" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_X_pos)
  "rr_prec_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_pos" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_X_inferred)
  "rr_prec_C_mul_X" " using "
    "coeff_ne" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_X_pos_inferred)
  "rr_prec_C_mul_X" " using "
    "coeff_pos" ":=" term :
  tactic

syntax (name := rr_prec_X_derivative_X_self)
  "rr_prec_X_derivative_X_self" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "nonneg_coeffs" ":=" term :
  tactic

syntax (name := rr_prec_X_derivative_X_self_inferred)
  "rr_prec_X_derivative_X_self" : tactic

syntax (name := rr_prec_wagner_derivative_gap_lag)
  "rr_prec_wagner_derivative_gap_lag" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_inferred)
  "rr_prec_wagner_derivative_gap_lag" : tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_den)
  "rr_prec_wagner_derivative_gap_lag_den" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence)
  "rr_prec_wagner_derivative_gap_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence_realrooted)
  "rr_prec_wagner_derivative_gap_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence_den)
  "rr_prec_wagner_derivative_gap_lag_sequence_den" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted)
  "rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_combo)
  "rr_prec_pos_X_lag_combo" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_combo_lag_pos)
  "rr_prec_pos_X_lag_combo" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence)
  "rr_prec_pos_X_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_natDegree_pos_X_lag_sequence)
  "rr_natDegree_pos_X_lag_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_natDegree_pos_X_lag_sequence_shifted)
  "rr_natDegree_pos_X_lag_sequence_shifted" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence_auto)
  "rr_prec_pos_X_lag_sequence_auto" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Automatic scalar-side-condition frontend for a positive-`X` lag sequence
with explicitly supplied current and lag coefficient functions. -/
syntax (name := rr_prec_pos_X_lag_coeff_sequence_auto)
  "rr_prec_pos_X_lag_coeff_sequence_auto" " using "
    "current_coeff" ":=" term ","
    "lag_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence_realrooted)
  "rr_prec_pos_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence_realrooted_auto)
  "rr_prec_pos_X_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Real-rootedness endpoint for
`rr_prec_pos_X_lag_coeff_sequence_auto`. -/
syntax (name := rr_prec_pos_X_lag_coeff_sequence_realrooted_auto)
  "rr_prec_pos_X_lag_coeff_sequence_realrooted_auto" " using "
    "current_coeff" ":=" term ","
    "lag_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_natDegree_pos_X_sub_C_lag_sequence)
  "rr_natDegree_pos_X_sub_C_lag_sequence" " using "
    "shift" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_natDegree_pos_X_sub_C_lag_sequence_shifted)
  "rr_natDegree_pos_X_sub_C_lag_sequence_shifted" " using "
    "shift" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_sub_C_lag_sequence)
  "rr_prec_pos_X_sub_C_lag_sequence" " using "
    "shift" ":=" term ","
    "base" ":=" term ","
    "shift_nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_sub_C_lag_sequence_realrooted)
  "rr_prec_pos_X_sub_C_lag_sequence_realrooted" " using "
    "shift" ":=" term ","
    "base" ":=" term ","
    "shift_nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_sub_C_lag_sequence_realrooted_auto)
  "rr_prec_pos_X_sub_C_lag_sequence_realrooted_auto" " using "
    "shift" ":=" term ","
    "base" ":=" term ","
    "shift_nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_unit_lag_sequence_auto)
  "rr_prec_pos_X_unit_lag_sequence_auto" " using "
    "current_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_unit_lag_sequence_realrooted_auto)
  "rr_prec_pos_X_unit_lag_sequence_realrooted_auto" " using "
    "current_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_same_coeff_sequence_auto)
  "rr_prec_pos_X_same_coeff_sequence_auto" " using "
    "shared_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_same_coeff_sequence_realrooted_auto)
  "rr_prec_pos_X_same_coeff_sequence_realrooted_auto" " using "
    "shared_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_wagner_pos) "rr_wagner_pos" : tactic

syntax (name := rr_wagner_pos_term) "rr_wagner_pos_term" : term

syntax (name := rr_wagner_pos_seq) "rr_wagner_pos_seq" : term

syntax (name := rr_wagner_recurrence_seq) "rr_wagner_recurrence_seq " term : term

macro_rules
  | `(tactic| rr_wagner_pos) =>
      `(tactic| rr_side_pos)
  | `(rr_wagner_pos_term) =>
      `(by rr_wagner_pos)
  | `(rr_wagner_pos_seq) =>
      `(fun n => by rr_wagner_pos)
  | `(rr_wagner_recurrence_seq $hrec:term) =>
      `(fun n => by simpa using $hrec n)



end Tactic
end RealRooted
