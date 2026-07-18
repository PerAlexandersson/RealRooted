import RealRooted.ClosedSegmentCountEqFromAnalytic
import RealRooted.CommonInterleaverTwo
import RealRooted.SameDegreeCountFromAnalytic

/-!
# Common-interleaver and compatibility tactic frontends

Thin wrappers for the proved Chudnovsky--Seymour easy directions and finite
common-interleaver upgrades.
-/

open Polynomial

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

syntax (name := rr_sameDegree_rootCountAbove_nonRoot_analytic_named)
  "rr_sameDegree_rootCountAbove_nonRoot_analytic" :
  tactic

syntax (name := rr_sameDegree_pair_common_interleaver_analytic_named)
  "rr_sameDegree_pair_common_interleaver_analytic" :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_local_lower_named)
  "rr_succDegree_pair_common_interleaver_local_lower" :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_leTwo_noGapTwo_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_leTwo_noGapTwo" " using "
    "le_two" ":=" term ","
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_compatible_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_compatible" " using "
    "root_count" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_closedSegmentCountEq_of_nonRoot_named)
  "rr_compatibleSuccDegree_closedSegmentCountEq_of_nonRoot" " using "
    "root_count" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_leTwo_of_nonRoot_named)
  "rr_compatibleSuccDegree_rootCountAbove_leTwo_of_nonRoot" " using "
    "root_count" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_noGapTwo_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_noGapTwo" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_closedSegment_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_closedSegment" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_countEq_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_countEq" " using "
    "count_eq" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_closedSegmentCountEq_iff_nonRoot_named)
  "rr_compatibleSuccDegree_closedSegmentCountEq_iff_nonRoot" :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_rightFamily_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_rightFamily" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSign_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSign" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower" " using "
    "no_gap" ":=" term :
  tactic

syntax (name := rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq_named)
  "rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq" " using "
    "count_eq" ":=" term :
  tactic

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_countEq_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_countEq" " using "
    "count_eq" ":=" term :
  tactic

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_closedSegment_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_closedSegment" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_rightFamily_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_rightFamily" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSign_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSign" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower" " using "
    "no_gap" ":=" term :
  tactic

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq" " using "
    "count_eq" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCrossing_named)
  "rr_succDegree_pair_common_interleaver_rootCrossing" " using "
    "root_crossing" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCount_named)
  "rr_succDegree_pair_common_interleaver_rootCount" " using "
    "root_count" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCountAbove_named)
  "rr_succDegree_pair_common_interleaver_rootCountAbove" " using "
    "root_count_above" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCountNonRoot_named)
  "rr_succDegree_pair_common_interleaver_rootCountNonRoot" " using "
    "root_count" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCountAboveNonRoot_named)
  "rr_succDegree_pair_common_interleaver_rootCountAboveNonRoot" " using "
    "root_count_above" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_closedSegmentCountEq_named)
  "rr_succDegree_pair_common_interleaver_closedSegmentCountEq" " using "
    "count_eq" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_closedSegmentNoGapTwo_named)
  "rr_succDegree_pair_common_interleaver_closedSegmentNoGapTwo" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rightFamilyNoGapTwo_named)
  "rr_succDegree_pair_common_interleaver_rightFamilyNoGapTwo" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_endpointSignNoGapTwo_named)
  "rr_succDegree_pair_common_interleaver_endpointSignNoGapTwo" " using "
    "no_gap_two" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_endpointSignLowerNoGap_named)
  "rr_succDegree_pair_common_interleaver_endpointSignLowerNoGap" " using "
    "no_gap" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_endpointSignLowerCountEq_named)
  "rr_succDegree_pair_common_interleaver_endpointSignLowerCountEq" " using "
    "count_eq" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountLeadRightZero_divXPrec_of_prec_named)
  "rr_succDegree_rootCountLeadRightZero_divXPrec_of_prec" " using "
    "orientation" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountLeadRightZero_of_divXPrec_named)
  "rr_succDegree_rootCountLeadRightZero_of_divXPrec" " using "
    "divX_prec" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountLead_of_bothNonzero_and_rightZero_named)
  "rr_succDegree_rootCountLead_of_bothNonzero_and_rightZero" " using "
    "both_nonzero" ":=" term ","
    "right_zero" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountLead_of_bothNonzero_and_divXPrec_named)
  "rr_succDegree_rootCountLead_of_bothNonzero_and_divXPrec" " using "
    "both_nonzero" ":=" term ","
    "divX_prec" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountResidual_of_prec_named)
  "rr_succDegree_rootCountResidual_of_prec" " using "
    "orientation" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCount_of_residual_and_lead_named)
  "rr_succDegree_rootCount_of_residual_and_lead" " using "
    "lead" ":=" term ","
    "residual" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountAbove_of_residual_and_lead_named)
  "rr_succDegree_rootCountAbove_of_residual_and_lead" " using "
    "lead" ":=" term ","
    "residual" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCrossing_of_residual_and_lead_named)
  "rr_succDegree_rootCrossing_of_residual_and_lead" " using "
    "lead" ":=" term ","
    "residual" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_residual_and_lead_named)
  "rr_succDegree_pair_common_interleaver_residual_and_lead" " using "
    "lead" ":=" term ","
    "residual" ":=" term :
  tactic

syntax
  (name := rr_succDegree_pair_common_interleaver_residual_bothNonzero_divXPrec_named)
  "rr_succDegree_pair_common_interleaver_residual_bothNonzero_divXPrec" " using "
    "both_nonzero" ":=" term ","
    "divX_prec" ":=" term ","
    "residual" ":=" term :
  tactic

syntax
  (name := rr_succDegree_pair_common_interleaver_residualPrec_bothNonzero_divXPrec_named)
  "rr_succDegree_pair_common_interleaver_residualPrec_bothNonzero_divXPrec" " using "
    "residual_prec" ":=" term ","
    "both_nonzero" ":=" term ","
    "divX_prec" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_degree_split_nonnegShift_named)
  "rr_compatible_pair_common_interleaver_degree_split_nonnegShift" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_rootCrossing_named)
  "rr_compatible_pair_common_interleaver_rootCrossing" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_rootCount_named)
  "rr_compatible_pair_common_interleaver_rootCount" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_rootCountAbove_named)
  "rr_compatible_pair_common_interleaver_rootCountAbove" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_rootCountNonRoot_named)
  "rr_compatible_pair_common_interleaver_rootCountNonRoot" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_rootCountAboveNonRoot_named)
  "rr_compatible_pair_common_interleaver_rootCountAboveNonRoot" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_degree_split_nonnegShift_named)
  "rr_pairwise_common_interleaver_degree_split_nonnegShift" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_rootCrossing_named)
  "rr_pairwise_common_interleaver_rootCrossing" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_rootCount_named)
  "rr_pairwise_common_interleaver_rootCount" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_rootCountAbove_named)
  "rr_pairwise_common_interleaver_rootCountAbove" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_rootCountNonRoot_named)
  "rr_pairwise_common_interleaver_rootCountNonRoot" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_rootCountAboveNonRoot_named)
  "rr_pairwise_common_interleaver_rootCountAboveNonRoot" " using "
    "same_degree" ":=" term ","
    "succ_degree" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_rootCrossing_named)
  "rr_chudnovskySeymour_fourWay_rootCrossing" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_rootCount_named)
  "rr_chudnovskySeymour_fourWay_rootCount" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_rootCountAbove_named)
  "rr_chudnovskySeymour_fourWay_rootCountAbove" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_rootCountNonRoot_named)
  "rr_chudnovskySeymour_fourWay_rootCountNonRoot" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_rootCountAboveNonRoot_named)
  "rr_chudnovskySeymour_fourWay_rootCountAboveNonRoot" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_rootCrossing_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_rootCrossing" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_rootCount_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_rootCount" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_rootCountAbove_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_rootCountAbove" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_rootCountNonRoot_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_rootCountNonRoot" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_commonInterleaver_rootCountAboveNonRoot_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_rootCountAboveNonRoot" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_rootCrossing_named)
  "rr_pairwiseCompatible_iff_familyCompatible_rootCrossing" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_rootCount_named)
  "rr_pairwiseCompatible_iff_familyCompatible_rootCount" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_rootCountAbove_named)
  "rr_pairwiseCompatible_iff_familyCompatible_rootCountAbove" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_rootCountNonRoot_named)
  "rr_pairwiseCompatible_iff_familyCompatible_rootCountNonRoot" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_familyCompatible_rootCountAboveNonRoot_named)
  "rr_pairwiseCompatible_iff_familyCompatible_rootCountAboveNonRoot" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_posCombo_pair_common_interleaver_degree_le_two_named)
  "rr_posCombo_pair_common_interleaver_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_splits" ":=" term ","
    "right_splits" ":=" term ","
    "pos_combo" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "right_degree_le_two" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_degree_le_two_named)
  "rr_compatible_pair_common_interleaver_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "right_degree_le_two" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_degree_le_one_named)
  "rr_pairwise_common_interleaver_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pairwise_common_interleaver_degree_le_two_named)
  "rr_pairwise_common_interleaver_degree_le_two" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_one_named)
  "rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_two_named)
  "rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_two" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

syntax (name := rr_pairwiseCommon_iff_commonInterleaver_degree_le_one_named)
  "rr_pairwiseCommon_iff_commonInterleaver_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pairwiseCommon_iff_commonInterleaver_degree_le_two_named)
  "rr_pairwiseCommon_iff_commonInterleaver_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

syntax (name := rr_commonInterleaver_iff_familyCompatible_degree_le_one_named)
  "rr_commonInterleaver_iff_familyCompatible_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_commonInterleaver_iff_familyCompatible_degree_le_two_named)
  "rr_commonInterleaver_iff_familyCompatible_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_degree_le_one_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_degree_le_two_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonLeft_degree_le_one_named)
  "rr_pairwiseCompatible_iff_commonLeft_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_degree_le_one_named)
  "rr_pairwiseCompatible_iff_familyCompatible_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_degree_le_two_named)
  "rr_pairwiseCompatible_iff_familyCompatible_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

syntax (name := rr_sameDegree_pair_common_interleaver_cubicInterior_named)
  "rr_sameDegree_pair_common_interleaver_cubicInterior" " using "
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

syntax (name := rr_noCommon_pair_common_interleaver_degree_le_three_named)
  "rr_noCommon_pair_common_interleaver_degree_le_three" " using "
    "below_certificate" ":=" term ","
    "above_certificate" ":=" term ","
    "succ_degree_endpoint" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_nonneg_coeffs" ":=" term ","
    "right_nonneg_coeffs" ":=" term ","
    "pos_combo" ":=" term ","
    "left_degree_le_right" ":=" term ","
    "right_degree_le_succ_left" ":=" term ","
    "no_common_roots" ":=" term ","
    "right_degree_le_three" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_compatible_comm using compatible := $h:term) =>
      `(tactic| exact RealRooted.Compatible.comm $h)
  | `(tactic|
      rr_compatible_comp_X_add_C using
        compatible := $h:term,
        shift := $r:term) =>
      `(tactic| exact RealRooted.Compatible.comp_X_add_C $h $r)
  | `(tactic|
      rr_compatible_reflect using
        compatible := $h:term,
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic|
        exact RealRooted.Compatible.reflect_of_natDegree_le $h $hfN $hgN)
  | `(tactic|
      rr_compatible_reflect_iff using
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic| exact RealRooted.Compatible.reflect_iff_natDegree_le $hfN $hgN)
  | `(tactic| rr_compatible_derivative using compatible := $h:term) =>
      `(tactic| exact RealRooted.Compatible.derivative $h)
  | `(tactic|
      rr_compatible_left_realrooted using
        compatible := $h:term,
        left_pos_lc := $hfpos:term) =>
      `(tactic| exact RealRooted.Compatible.isRealRooted_left $h $hfpos)
  | `(tactic|
      rr_compatible_right_realrooted using
        compatible := $h:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic| exact RealRooted.Compatible.isRealRooted_right $h $hgpos)
  | `(tactic|
      rr_compatible_right_degree_le_succ using
        compatible := $h:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic| exact RealRooted.Compatible.natDegree_right_le_succ
        $h $hfpos $hgpos)
  | `(tactic|
      rr_compatible_degree_close using
        compatible := $h:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic| exact RealRooted.Compatible.natDegree_close $h $hfpos $hgpos)
  | `(tactic|
      rr_compatible_to_pos_combo using
        compatible := $h:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic| exact RealRooted.Compatible.toPosComboRealRooted
        $h $hfpos $hgpos)
  | `(tactic|
      rr_compatible_of_pos_combo using
        pos_combo := $hfg:term,
        left_realrooted := $hf:term,
        right_realrooted := $hg:term) =>
      `(tactic| exact RealRooted.Compatible.of_posComboRealRooted $hfg $hf $hg)
  | `(tactic|
      rr_compatible_of_pos_combo_same_degree using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic| exact RealRooted.Compatible.of_posComboRealRooted_sameDegree
        $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_compatible_of_pos_combo_succ_degree using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hdeg:term,
        left_splits := $hfsplits:term) =>
      `(tactic| exact RealRooted.Compatible.of_posComboRealRooted_succDegree
        $hfg $hfpos $hgpos $hdeg $hfsplits)
  | `(tactic|
      rr_compatible_of_common_left using
        common_to_left := $hhf:term,
        common_to_right := $hhg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic| exact RealRooted.Compatible.of_commonLeftInterleaver
        $hhf $hhg $hfpos $hgpos)
  | `(tactic|
      rr_compatible_of_common_right using
        left_to_common := $hfh:term,
        right_to_common := $hgh:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic| exact RealRooted.Compatible.of_commonInterleaver
        $hfh $hgh $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_comp_X_add_C using
        pos_combo := $hfg:term,
        shift := $r:term) =>
      `(tactic| exact RealRooted.PosComboRealRooted.comp_X_add_C $hfg $r)
  | `(tactic|
      rr_pairwise_compatible_of_common_left using
        common_left := $hcommon:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.pairwiseCompatible_of_commonLeftInterleaver
          $hcommon $hpos)
  | `(tactic|
      rr_pairwise_compatible_of_pairwise_common_left using
        pairwise_common_left := $hpair:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.pairwiseCompatible_of_pairwiseHasCommonLeftInterleaver
          $hpair $hpos)
  | `(tactic|
      rr_pairwise_compatible_of_common_right using
        common_right := $hcommon:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.pairwiseCompatible_of_commonInterleaver $hcommon $hpos)
  | `(tactic|
      rr_pairwise_compatible_of_pairwise_common_right using
        pairwise_common_right := $hpair:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.pairwiseCompatible_of_pairwiseHasCommonInterleaver
          $hpair $hpos)
  | `(tactic|
      rr_common_interleaver_of_pairwise using
        member_splits := $hrr:term,
        member_pos_lc := $hpos:term,
        pairwise_common := $hpair:term) =>
      `(tactic|
        exact RealRooted.hasCommonInterleaver_of_pairwiseHasCommonInterleaver
          $hrr $hpos $hpair)
  | `(tactic|
      rr_common_left_interleaver_of_pairwise using
        member_splits := $hrr:term,
        member_pos_lc := $hpos:term,
        pairwise_common_left := $hpair:term) =>
      `(tactic|
        exact
          RealRooted.hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver
            $hrr $hpos $hpair)
  | `(tactic| rr_common_interleaver_family_upgrade) =>
      `(tactic| exact RealRooted.commonInterleaverFamilyUpgrade)
  | `(tactic| rr_common_left_interleaver_family_upgrade) =>
      `(tactic| exact RealRooted.commonLeftInterleaverFamilyUpgrade)
  | `(tactic|
      rr_common_interleaver_sum_realrooted using
        common_right := $hcommon:term,
        member_pos_lc := $hpos:term,
        nonempty := $hne:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_sum_of_commonInterleaver
          $hcommon $hpos $hne)
  | `(tactic|
      rr_common_left_interleaver_sum_realrooted using
        common_left := $hcommon:term,
        member_pos_lc := $hpos:term,
        nonempty := $hne:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_sum_of_commonLeftInterleaver
          $hcommon $hpos $hne)
  | `(tactic| rr_sameDegree_rootCountAbove_nonRoot_analytic) =>
      `(tactic|
        exact
          RealRooted.posComboNoCommonSameDegreeRootCountAboveNonRootNonneg_from_analytic)
  | `(tactic| rr_sameDegree_pair_common_interleaver_analytic) =>
      `(tactic|
        exact
          RealRooted.posComboNoCommonSameDegreePairHasCommonInterleaverNonneg_from_analytic)
  | `(tactic| rr_succDegree_pair_common_interleaver_local_lower) =>
      `(tactic|
        exact
          RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_local_lower_counts)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_leTwo_noGapTwo using
        le_two := $hle2:term,
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo
          $hle2 $hgap)
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_compatible using
        root_count := $hcount:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
          $hcount)
  | `(tactic|
      rr_compatibleSuccDegree_closedSegmentCountEq_of_nonRoot using
        root_count := $hcount:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeClosedSegmentCountEq_of_nonRoot
          $hcount)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_leTwo_of_nonRoot using
        root_count := $hcount:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveLeTwo_of_nonRoot
          $hcount)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_noGapTwo using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
          $hgap)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_closedSegment using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegment
          $hgap)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_countEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact
          RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
            $hcount)
  | `(tactic| rr_compatibleSuccDegree_closedSegmentCountEq_iff_nonRoot) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeClosedSegmentCountEq_iff_nonRoot)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_rightFamily using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_rightFamily
          $hgap)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSign using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSign
          $hgap)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower using
        no_gap := $hgap:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSignLower
          $hgap)
  | `(tactic|
      rr_compatibleSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact RealRooted.compatibleSuccDegreeRootCountAboveNonRoot_of_lowerCountEq
          $hcount)
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_countEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
          $hcount)
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_closedSegment using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentNoGapTwo
          $hgap)
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_rightFamily using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_rightFamilyNoGapTwo
          $hgap)
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSign using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignNoGapTwo
          $hgap)
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_endpointSignLower using
        no_gap := $hgap:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignLower
          $hgap)
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_lowerCountEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_lowerCountEq
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCrossing using
        root_crossing := $hcross:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
          $hcross)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCount using
        root_count := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rootCount
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCountAbove using
        root_count_above := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCountNonRoot using
        root_count := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCountAboveNonRoot using
        root_count_above := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_closedSegmentCountEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_closedSegmentNoGapTwo using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentNoGapTwo
          $hgap)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rightFamilyNoGapTwo using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rightFamilyNoGapTwo
          $hgap)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_endpointSignNoGapTwo using
        no_gap_two := $hgap:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_endpointSignNoGapTwo
          $hgap)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_endpointSignLowerNoGap using
        no_gap := $hgap:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_endpointSignLower
          $hgap)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_endpointSignLowerCountEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_lowerCountEq
          $hcount)
  | `(tactic|
      rr_succDegree_rootCountLeadRightZero_divXPrec_of_prec using
        orientation := $horient:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrec_of_precFG
          $horient)
  | `(tactic|
      rr_succDegree_rootCountLeadRightZero_of_divXPrec using
        divX_prec := $hdivX:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_prec
          $hdivX)
  | `(tactic|
      rr_succDegree_rootCountLead_of_bothNonzero_and_rightZero using
        both_nonzero := $hboth:term,
        right_zero := $hright:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_rightZero
          $hboth $hright)
  | `(tactic|
      rr_succDegree_rootCountLead_of_bothNonzero_and_divXPrec using
        both_nonzero := $hboth:term,
        divX_prec := $hdivX:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_divX_prec
          $hboth $hdivX)
  | `(tactic|
      rr_succDegree_rootCountResidual_of_prec using
        orientation := $horient:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountResidual_of_prec
          $horient)
  | `(tactic|
      rr_succDegree_rootCount_of_residual_and_lead using
        lead := $hlead:term,
        residual := $hres:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCount_of_residual_and_lead
          $hlead $hres)
  | `(tactic|
      rr_succDegree_rootCountAbove_of_residual_and_lead using
        lead := $hlead:term,
        residual := $hres:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAbove_of_residual_and_lead
          $hlead $hres)
  | `(tactic|
      rr_succDegree_rootCrossing_of_residual_and_lead using
        lead := $hlead:term,
        residual := $hres:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_residual_and_lead
          $hlead $hres)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_residual_and_lead using
        lead := $hlead:term,
        residual := $hres:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_residual_and_lead
          $hlead $hres)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_residual_bothNonzero_divXPrec using
        both_nonzero := $hboth:term,
        divX_prec := $hdivX:term,
        residual := $hres:term) =>
      `(tactic|
        exact
          RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_residual_bothNonzero_divX_prec
            $hboth $hdivX $hres)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_residualPrec_bothNonzero_divXPrec using
        residual_prec := $hres:term,
        both_nonzero := $hboth:term,
        divX_prec := $hdivX:term) =>
      `(tactic|
        exact
          RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_residualPrec_bothNonzero_divX_prec
            $hres $hboth $hdivX)
  | `(tactic|
      rr_compatible_pair_common_interleaver_degree_split_nonnegShift using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
          $hsame $hsucc)
  | `(tactic|
      rr_compatible_pair_common_interleaver_rootCrossing using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_rootCrossing
          $hsame $hsucc)
  | `(tactic|
      rr_compatible_pair_common_interleaver_rootCount using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_rootCount
          $hsame $hsucc)
  | `(tactic|
      rr_compatible_pair_common_interleaver_rootCountAbove using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_rootCountAboveBoth
          $hsame $hsucc)
  | `(tactic|
      rr_compatible_pair_common_interleaver_rootCountNonRoot using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_rootCountNonRoot
          $hsame $hsucc)
  | `(tactic|
      rr_compatible_pair_common_interleaver_rootCountAboveNonRoot using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_rootCountAboveBothNonRoot
          $hsame $hsucc)
  | `(tactic|
      rr_pairwise_common_interleaver_degree_split_nonnegShift using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_via_nonnegShift
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCrossing using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCount using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCountAbove using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCountNonRoot using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountNonRoot
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_pairwise_common_interleaver_rootCountAboveNonRoot using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term,
        member_pos_lc := $hpos:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBothNonRoot
          $hsame $hsucc $hpos $hpair)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCrossing using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCount using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCount $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCount $hsucc))
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCountAbove using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove $hsucc))
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCountNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot
            $hsucc))
  | `(tactic|
      rr_chudnovskySeymour_fourWay_rootCountAboveNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCrossing using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCount using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCount $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCount $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCountAbove using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCountNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_rootCountAboveNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCrossing using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos $hsame $hsucc)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCount using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCount $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCount $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCountAbove using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCountNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot
            $hsucc))
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_rootCountAboveNonRoot using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_rootCrossing
          $hrr $hpos
          (RealRooted.posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsame)
          (RealRooted.posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot
            $hsucc))
  | `(tactic|
      rr_posCombo_pair_common_interleaver_degree_le_two using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_splits := $hfsplit:term,
        right_splits := $hgsplit:term,
        pos_combo := $hfg:term,
        left_degree_le_two := $hfdeg:term,
        right_degree_le_two := $hgdeg:term) =>
      `(tactic|
        exact RealRooted.posComboPairHasCommonInterleaver_of_natDegree_le_two
          $hfpos $hgpos $hfsplit $hgsplit $hfg $hfdeg $hgdeg)
  | `(tactic|
      rr_compatible_pair_common_interleaver_degree_le_two using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        compatible := $hfg:term,
        left_degree_le_two := $hfdeg:term,
        right_degree_le_two := $hgdeg:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_natDegree_le_two
          $hfpos $hgpos $hfg $hfdeg $hgdeg)
  | `(tactic|
      rr_pairwise_common_interleaver_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact RealRooted.pairwiseHasCommonInterleaver_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_pairwise_common_interleaver_degree_le_two using
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term,
        pairwise_compatible := $hpair:term) =>
      `(tactic|
        exact RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_natDegree_le_two
          $hpos $hdeg $hpair)
  | `(tactic|
      rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_two using
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_two
          $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCommon_iff_commonInterleaver_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCommon_iff_commonInterleaver_degree_le_two using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term) =>
      `(tactic|
        exact pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_natDegree_le_two
          $hrr $hpos $hdeg)
  | `(tactic|
      rr_commonInterleaver_iff_familyCompatible_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact hasCommonInterleaver_iff_familyCompatible_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_commonInterleaver_iff_familyCompatible_degree_le_two using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term) =>
      `(tactic|
        exact hasCommonInterleaver_iff_familyCompatible_of_natDegree_le_two
          $hrr $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonInterleaver_degree_le_two using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_two
          $hrr $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCompatible_iff_commonLeft_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_commonLeftInterleaver_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_pairwiseCompatible_iff_familyCompatible_degree_le_two using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term) =>
      `(tactic|
        exact pairwiseCompatible_iff_familyCompatible_of_natDegree_le_two
          $hrr $hpos $hdeg)
  | `(tactic|
      rr_sameDegree_pair_common_interleaver_cubicInterior using
        below_certificate := $hbelow:term,
        above_certificate := $habove:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term) =>
      `(tactic|
        exact sameDegreePairHasCommonInterleaver_nonneg_of_natDegree_le_three_of_cubicInterior
          $hbelow $habove $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_noCommon_pair_common_interleaver_degree_le_three using
        below_certificate := $hbelow:term,
        above_certificate := $habove:term,
        succ_degree_endpoint := $hsucc:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        left_degree_le_right := $hdeg_lo:term,
        right_degree_le_succ_left := $hdeg_hi:term,
        no_common_roots := $hno:term,
        right_degree_le_three := $hgdeg:term) =>
      `(tactic|
        exact posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_three_and_succDegree
          $hbelow $habove $hsucc $hfpos $hgpos $hfnn $hgnn $hfg
          $hdeg_lo $hdeg_hi $hno $hgdeg)

end Tactic
end RealRooted
