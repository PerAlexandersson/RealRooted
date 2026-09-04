import RealRooted.Tactic.RootCount.SequenceCore

/-!
# Core root-count tactic syntax

Parser declarations for general root-count and local-continuity certificates.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_natDegree_add_C_mul_lt_named)
  "rr_natDegree_add_C_mul_lt" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

syntax (name := rr_natDegree_add_C_mul_lt_sequence_named)
  "rr_natDegree_add_C_mul_lt_sequence" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

syntax (name := rr_leadingCoeff_add_C_mul_lt_named)
  "rr_leadingCoeff_add_C_mul_lt" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

syntax (name := rr_leadingCoeff_add_C_mul_lt_sequence_named)
  "rr_leadingCoeff_add_C_mul_lt_sequence" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

syntax (name := rr_exists_root_lt_succDegree_add_right_small_named)
  "rr_exists_root_lt_succDegree_add_right_small" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "bound" ":=" term :
  tactic

syntax (name := rr_exists_root_lt_succDegree_add_right_small_sequence_named)
  "rr_exists_root_lt_succDegree_add_right_small_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "bound" ":=" term :
  tactic

syntax (name := rr_degreeIncreasing_local_lower_count_named)
  "rr_degreeIncreasing_local_lower_count" " using "
    "left_splits" ":=" term ","
    "degree_lt" ":=" term ","
    "radius" ":=" term ","
    "radius_pos" ":=" term :
  tactic

syntax (name := rr_degreeIncreasing_local_lower_count_sequence_named)
  "rr_degreeIncreasing_local_lower_count_sequence" " using "
    "left_splits" ":=" term ","
    "degree_lt" ":=" term ","
    "radius" ":=" term ","
    "radius_pos" ":=" term :
  tactic

syntax (name := rr_positiveParameter_local_lower_count_named)
  "rr_positiveParameter_local_lower_count" " using "
    "splits_on_interval" ":=" term ","
    "degree_on_interval" ":=" term ","
    "parameter_mem" ":=" term ","
    "radius_pos" ":=" term :
  tactic

syntax (name := rr_positiveParameter_local_lower_count_sequence_named)
  "rr_positiveParameter_local_lower_count_sequence" " using "
    "splits_on_interval" ":=" term ","
    "degree_on_interval" ":=" term ","
    "parameter_mem" ":=" term ","
    "radius_pos" ":=" term :
  tactic

syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_named)
  "rr_rightFamily_card_roots_gt_eq_zero_param" " using "
    "parameter_pos" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_inferred)
  "rr_rightFamily_card_roots_gt_eq_zero_param" : tactic

syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_sequence_named)
  "rr_rightFamily_card_roots_gt_eq_zero_param_sequence" " using "
    "parameter_pos" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_sequence_inferred)
  "rr_rightFamily_card_roots_gt_eq_zero_param_sequence" : tactic

syntax (name := rr_rightFamily_card_roots_gt_eq_local_lower_named)
  "rr_rightFamily_card_roots_gt_eq_local_lower" " using "
    "interval_order" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term ","
    "local_lower" ":=" term :
  tactic

syntax (name := rr_rightFamily_card_roots_gt_eq_local_lower_sequence_named)
  "rr_rightFamily_card_roots_gt_eq_local_lower_sequence" " using "
    "interval_order" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term ","
    "local_lower" ":=" term :
  tactic

syntax (name := rr_card_filter_gt_endpoint_eq_local_lower_named)
  "rr_card_filter_gt_endpoint_eq_local_lower" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term ","
    "threshold_not_left_root" ":=" term ","
    "small_local_lower" ":=" term ","
    "right_family_splits" ":=" term ","
    "right_family_not_root" ":=" term ","
    "swapped_family_splits" ":=" term ","
    "swapped_family_not_root" ":=" term :
  tactic

syntax (name := rr_card_filter_gt_endpoint_eq_local_lower_sequence_named)
  "rr_card_filter_gt_endpoint_eq_local_lower_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term ","
    "threshold_not_left_root" ":=" term ","
    "small_local_lower" ":=" term ","
    "right_family_splits" ":=" term ","
    "right_family_not_root" ":=" term ","
    "swapped_family_splits" ":=" term ","
    "swapped_family_not_root" ":=" term :
  tactic

syntax (name := rr_closedSegment_eval_ne_zero_same_sign_named)
  "rr_closedSegment_eval_ne_zero_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_closedSegment_eval_ne_zero_same_sign_sequence_named)
  "rr_closedSegment_eval_ne_zero_same_sign_sequence" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_closedSegment_not_isRoot_same_sign_named)
  "rr_closedSegment_not_isRoot_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_closedSegment_not_isRoot_same_sign_sequence_named)
  "rr_closedSegment_not_isRoot_same_sign_sequence" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_rightFamily_eval_ne_zero_same_sign_named)
  "rr_rightFamily_eval_ne_zero_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_rightFamily_eval_ne_zero_same_sign_sequence_named)
  "rr_rightFamily_eval_ne_zero_same_sign_sequence" " using "
    "parameter_nonneg" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_exists_threshold_no_mem_Ioc_named)
  "rr_exists_threshold_no_mem_Ioc" :
  tactic

syntax (name := rr_exists_threshold_no_mem_Ioc_sequence_named)
  "rr_exists_threshold_no_mem_Ioc_sequence" :
  tactic

syntax (name := rr_exists_nonRoot_threshold_count_eq_named)
  "rr_exists_nonRoot_threshold_count_eq" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_exists_nonRoot_threshold_count_eq_sequence_named)
  "rr_exists_nonRoot_threshold_count_eq_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term :
  tactic

syntax (name := rr_exists_nonRoot_threshold_count_gt_eq_named)
  "rr_exists_nonRoot_threshold_count_gt_eq" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_exists_nonRoot_threshold_count_gt_eq_sequence_named)
  "rr_exists_nonRoot_threshold_count_gt_eq_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term :
  tactic

syntax (name := rr_rootCount_diff_le_one_nonRoot_named)
  "rr_rootCount_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_diff_le_one_nonRoot_sequence_named)
  "rr_rootCount_diff_le_one_nonRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_abs_diff_le_one_nonRoot_named)
  "rr_rootCount_abs_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_abs_diff_le_one_nonRoot_sequence_named)
  "rr_rootCount_abs_diff_le_one_nonRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_diff_le_one_nonRoot_isRoot_named)
  "rr_rootCount_diff_le_one_nonRoot_isRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_diff_le_one_nonRoot_isRoot_sequence_named)
  "rr_rootCount_diff_le_one_nonRoot_isRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_named)
  "rr_rootCountAbove_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_sequence_named)
  "rr_rootCountAbove_diff_le_one_nonRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_isRoot_named)
  "rr_rootCountAbove_diff_le_one_nonRoot_isRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_isRoot_sequence_named)
  "rr_rootCountAbove_diff_le_one_nonRoot_isRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_max_abs_diff_le_one_named)
  "rr_rootCount_max_abs_diff_le_one" " using "
    "bundled_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_max_abs_diff_le_one_sequence_named)
  "rr_rootCount_max_abs_diff_le_one_sequence" " using "
    "bundled_bound" ":=" term :
  tactic

syntax (name := rr_left_card_roots_succDegree_named)
  "rr_left_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_left_card_roots_succDegree_sequence_named)
  "rr_left_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_right_card_roots_succDegree_named)
  "rr_right_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_right_card_roots_succDegree_sequence_named)
  "rr_right_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_left_ne_zero_card_roots_succDegree_named)
  "rr_left_ne_zero_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_left_ne_zero_card_roots_succDegree_sequence_named)
  "rr_left_ne_zero_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_right_ne_zero_card_roots_succDegree_named)
  "rr_right_ne_zero_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_right_ne_zero_card_roots_succDegree_sequence_named)
  "rr_right_ne_zero_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_mono_named)
  "rr_card_roots_filter_le_mono" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_mono_sequence_named)
  "rr_card_roots_filter_le_mono_sequence" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_antitone_named)
  "rr_card_roots_filter_gt_antitone" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_antitone_sequence_named)
  "rr_card_roots_filter_gt_antitone_sequence" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_mono_named)
  "rr_card_roots_filter_le_and_gt_mono" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_mono_sequence_named)
  "rr_card_roots_filter_le_and_gt_mono_sequence" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

end Tactic
end RealRooted
