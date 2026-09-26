import RealRooted.Tactic.CommonInterleaver.BasicSyntax

/-!
# Analytic common-interleaver tactic syntax

Parser declarations for root-count certificates and two-polynomial
common-interleaver endpoints.
-/

namespace RealRooted
namespace Tactic

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

syntax (name := rr_succDegree_rootCountLeadRightZero_divXStrictInterl_of_strict_interl_named)
  "rr_succDegree_rootCountLeadRightZero_divXStrictInterl_of_strict_interl" " using "
    "orientation" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountLeadRightZero_of_divXStrictInterl_named)
  "rr_succDegree_rootCountLeadRightZero_of_divXStrictInterl" " using "
    "divX_strictInterl" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountLead_of_bothNonzero_and_rightZero_named)
  "rr_succDegree_rootCountLead_of_bothNonzero_and_rightZero" " using "
    "both_nonzero" ":=" term ","
    "right_zero" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountLead_of_bothNonzero_and_divXStrictInterl_named)
  "rr_succDegree_rootCountLead_of_bothNonzero_and_divXStrictInterl" " using "
    "both_nonzero" ":=" term ","
    "divX_strictInterl" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountResidual_of_strict_interl_named)
  "rr_succDegree_rootCountResidual_of_strict_interl" " using "
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
  (name := rr_succDegree_pair_common_interleaver_residual_bothNonzero_divXStrictInterl_named)
  "rr_succDegree_pair_common_interleaver_residual_bothNonzero_divXStrictInterl" " using "
    "both_nonzero" ":=" term ","
    "divX_strictInterl" ":=" term ","
    "residual" ":=" term :
  tactic

syntax
  (name := rr_succDegree_pair_common_interleaver_residualStrictInterl_bothNonzero_divXStrictInterl_named)
  "rr_succDegree_pair_common_interleaver_residualStrictInterl_bothNonzero_divXStrictInterl" " using "
    "residual_strictInterl" ":=" term ","
    "both_nonzero" ":=" term ","
    "divX_strictInterl" ":=" term :
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

syntax
  (name := rr_chudnovskySeymour_compatible_pair_common_interleaver_statement_named)
  "rr_chudnovskySeymour_compatible_pair_common_interleaver_statement" :
  tactic

syntax
  (name := rr_chudnovskySeymour_compatible_pair_common_left_interleaver_statement_named)
  "rr_chudnovskySeymour_compatible_pair_common_left_interleaver_statement" :
  tactic

syntax (name := rr_chudnovskySeymour_compatible_pair_common_interleaver_named)
  "rr_chudnovskySeymour_compatible_pair_common_interleaver" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_compatible_pair_common_left_interleaver_named)
  "rr_chudnovskySeymour_compatible_pair_common_left_interleaver" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term :
  tactic

end Tactic
end RealRooted
/- Parser compatibility for the pre-#984 Prec/Prec0 tactic surface.
    Canonical syntax is preferred; these declarations retain old scripts
    and dispatch through the deprecated theorem aliases above. -/
namespace RealRooted
namespace Tactic
syntax (name := rr_succDegree_rootCountLeadRightZero_divXPrec_of_prec_named_legacy)
  "rr_succDegree_rootCountLeadRightZero_divXPrec_of_prec" " using "
    "orientation" ":=" term :
  tactic

syntax (name := rr_succDegree_rootCountResidual_of_prec_named_legacy)
  "rr_succDegree_rootCountResidual_of_prec" " using "
    "orientation" ":=" term :
  tactic

end Tactic
end RealRooted
