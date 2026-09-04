import RealRooted.Tactic.CommonInterleaver.Core

/-!
# Basic common-interleaver tactic syntax

Parser declarations for compatibility transports, finite-family upgrades, and
their pointwise sequence forms.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_compatible_comm_named)
  "rr_compatible_comm" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_compatible_comp_X_add_C_named)
  "rr_compatible_comp_X_add_C" " using "
    "compatible" ":=" term ","
    "shift" ":=" term :
  tactic

syntax (name := rr_compatible_reflect_named)
  "rr_compatible_reflect" " using "
    "compatible" ":=" term ","
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

syntax (name := rr_compatible_reflect_iff_named)
  "rr_compatible_reflect_iff" " using "
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

syntax (name := rr_compatible_derivative_named)
  "rr_compatible_derivative" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_compatible_left_realrooted_named)
  "rr_compatible_left_realrooted" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_right_realrooted_named)
  "rr_compatible_right_realrooted" " using "
    "compatible" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_right_degree_le_succ_named)
  "rr_compatible_right_degree_le_succ" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_degree_close_named)
  "rr_compatible_degree_close" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_to_pos_combo_named)
  "rr_compatible_to_pos_combo" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_of_pos_combo_named)
  "rr_compatible_of_pos_combo" " using "
    "pos_combo" ":=" term ","
    "left_realrooted" ":=" term ","
    "right_realrooted" ":=" term :
  tactic

syntax (name := rr_compatible_of_pos_combo_same_degree_named)
  "rr_compatible_of_pos_combo_same_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

syntax (name := rr_compatible_of_pos_combo_succ_degree_named)
  "rr_compatible_of_pos_combo_succ_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_comm_named)
  "rr_compatible_sequence_comm" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_comp_X_add_C_named)
  "rr_compatible_sequence_comp_X_add_C" " using "
    "compatible" ":=" term ","
    "shift" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_reflect_named)
  "rr_compatible_sequence_reflect" " using "
    "compatible" ":=" term ","
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_reflect_iff_named)
  "rr_compatible_sequence_reflect_iff" " using "
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_derivative_named)
  "rr_compatible_sequence_derivative" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_left_realrooted_named)
  "rr_compatible_sequence_left_realrooted" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_right_realrooted_named)
  "rr_compatible_sequence_right_realrooted" " using "
    "compatible" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_right_degree_le_succ_named)
  "rr_compatible_sequence_right_degree_le_succ" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_degree_close_named)
  "rr_compatible_sequence_degree_close" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_to_pos_combo_named)
  "rr_compatible_sequence_to_pos_combo" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_of_pos_combo_named)
  "rr_compatible_sequence_of_pos_combo" " using "
    "pos_combo" ":=" term ","
    "left_realrooted" ":=" term ","
    "right_realrooted" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_of_pos_combo_same_degree_named)
  "rr_compatible_sequence_of_pos_combo_same_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_of_pos_combo_succ_degree_named)
  "rr_compatible_sequence_of_pos_combo_succ_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term :
  tactic

syntax (name := rr_compatible_of_common_left_named)
  "rr_compatible_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_of_common_right_named)
  "rr_compatible_of_common_right" " using "
    "left_to_common" ":=" term ","
    "right_to_common" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_pos_combo_comp_X_add_C_named)
  "rr_pos_combo_comp_X_add_C" " using "
    "pos_combo" ":=" term ","
    "shift" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_of_common_left_named)
  "rr_compatible_sequence_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_compatible_sequence_of_common_right_named)
  "rr_compatible_sequence_of_common_right" " using "
    "left_to_common" ":=" term ","
    "right_to_common" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_pos_combo_sequence_comp_X_add_C_named)
  "rr_pos_combo_sequence_comp_X_add_C" " using "
    "pos_combo" ":=" term ","
    "shift" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_of_common_left_named)
  "rr_pairwise_compatible_of_common_left" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_of_pairwise_common_left_named)
  "rr_pairwise_compatible_of_pairwise_common_left" " using "
    "pairwise_common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_of_common_right_named)
  "rr_pairwise_compatible_of_common_right" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_of_pairwise_common_right_named)
  "rr_pairwise_compatible_of_pairwise_common_right" " using "
    "pairwise_common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_common_interleaver_of_pairwise_named)
  "rr_common_interleaver_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common" ":=" term :
  tactic

syntax (name := rr_common_left_interleaver_of_pairwise_named)
  "rr_common_left_interleaver_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common_left" ":=" term :
  tactic

syntax (name := rr_common_interleaver_family_upgrade_named)
  "rr_common_interleaver_family_upgrade" :
  tactic

syntax (name := rr_common_left_interleaver_family_upgrade_named)
  "rr_common_left_interleaver_family_upgrade" :
  tactic

syntax (name := rr_common_interleaver_sum_realrooted_named)
  "rr_common_interleaver_sum_realrooted" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

syntax (name := rr_common_left_interleaver_sum_realrooted_named)
  "rr_common_left_interleaver_sum_realrooted" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_sequence_of_common_left_named)
  "rr_pairwise_compatible_sequence_of_common_left" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_sequence_of_pairwise_common_left_named)
  "rr_pairwise_compatible_sequence_of_pairwise_common_left" " using "
    "pairwise_common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_sequence_of_common_right_named)
  "rr_pairwise_compatible_sequence_of_common_right" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_pairwise_compatible_sequence_of_pairwise_common_right_named)
  "rr_pairwise_compatible_sequence_of_pairwise_common_right" " using "
    "pairwise_common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_common_interleaver_sequence_of_pairwise_named)
  "rr_common_interleaver_sequence_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common" ":=" term :
  tactic

syntax (name := rr_common_left_interleaver_sequence_of_pairwise_named)
  "rr_common_left_interleaver_sequence_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common_left" ":=" term :
  tactic

syntax (name := rr_common_interleaver_sum_sequence_realrooted_named)
  "rr_common_interleaver_sum_sequence_realrooted" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

syntax (name := rr_common_left_interleaver_sum_sequence_realrooted_named)
  "rr_common_left_interleaver_sum_sequence_realrooted" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

end Tactic
end RealRooted
