import RealRooted.Tactic.RootCount.CoreSyntax
import RealRooted.Tactic.RootCount.LowDegree

/-!
# Low-degree root-count tactic syntax

Parser declarations for same-degree and low-degree root-count certificates.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_rightFamily_sameDegree_gt_count_eq_named)
  "rr_rightFamily_sameDegree_gt_count_eq" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_parameter_nonneg" ":=" term ","
    "interval_order" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

syntax (name := rr_rightFamily_sameDegree_gt_count_eq_sequence_named)
  "rr_rightFamily_sameDegree_gt_count_eq_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_parameter_nonneg" ":=" term ","
    "interval_order" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

syntax (name := rr_rightFamily_zero_one_gt_count_eq_named)
  "rr_rightFamily_zero_one_gt_count_eq" " using "
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

syntax (name := rr_rightFamily_zero_one_gt_count_eq_sequence_named)
  "rr_rightFamily_zero_one_gt_count_eq_sequence" " using "
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

syntax (name := rr_sameDegree_gt_count_eq_no_rightFamily_named)
  "rr_sameDegree_gt_count_eq_no_rightFamily" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

syntax (name := rr_sameDegree_gt_count_eq_no_rightFamily_sequence_named)
  "rr_sameDegree_gt_count_eq_no_rightFamily_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCountAbove_no_rightFamily_named)
  "rr_sameDegree_rootCountAbove_no_rightFamily" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCountAbove_no_rightFamily_sequence_named)
  "rr_sameDegree_rootCountAbove_no_rightFamily_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCountAbove_no_pos_crossing_named)
  "rr_sameDegree_rootCountAbove_no_pos_crossing" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "no_positive_crossing" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCountAbove_no_pos_crossing_sequence_named)
  "rr_sameDegree_rootCountAbove_no_pos_crossing_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "no_positive_crossing" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCountAbove_pos_crossing_named)
  "rr_sameDegree_rootCountAbove_pos_crossing" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "positive_crossing" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCountAbove_pos_crossing_sequence_named)
  "rr_sameDegree_rootCountAbove_pos_crossing_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "positive_crossing" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_two_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_two_sequence_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_two_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_two_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCrossing_degree_le_one_named)
  "rr_sameDegree_rootCrossing_degree_le_one" " using "
    "left_degree_le_one" ":=" term :
  tactic

syntax (name := rr_sameDegree_rootCrossing_degree_le_one_sequence_named)
  "rr_sameDegree_rootCrossing_degree_le_one_sequence" " using "
    "left_degree_le_one" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_two_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_three_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_three" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_three_sequence_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_three_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_three_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_three" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_three_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_three" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

syntax (name := rr_compatible_succDegree_rootCountAbove_le_two_named)
  "rr_compatible_succDegree_rootCountAbove_le_two" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_compatible_succDegree_rootCountAbove_le_two_sequence_named)
  "rr_compatible_succDegree_rootCountAbove_le_two_sequence" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCount_cubicInterior_named)
  "rr_posCombo_sameDegree_rootCount_cubicInterior" " using "
    "below_certificate" ":=" term ","
    "above_certificate" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCount_cubicInterior_sequence_named)
  "rr_posCombo_sameDegree_rootCount_cubicInterior_sequence" " using "
    "below_certificate" ":=" term ","
    "above_certificate" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCountAbove_cubicInterior_named)
  "rr_posCombo_sameDegree_rootCountAbove_cubicInterior" " using "
    "below_certificate" ":=" term ","
    "above_certificate" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCountAbove_cubicInterior_sequence_named)
  "rr_posCombo_sameDegree_rootCountAbove_cubicInterior_sequence" " using "
    "below_certificate" ":=" term ","
    "above_certificate" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCrossing_cubicInterior_named)
  "rr_posCombo_sameDegree_rootCrossing_cubicInterior" " using "
    "below_certificate" ":=" term ","
    "above_certificate" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

syntax (name := rr_posCombo_sameDegree_rootCrossing_cubicInterior_sequence_named)
  "rr_posCombo_sameDegree_rootCrossing_cubicInterior_sequence" " using "
    "below_certificate" ":=" term ","
    "above_certificate" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

end Tactic
end RealRooted
