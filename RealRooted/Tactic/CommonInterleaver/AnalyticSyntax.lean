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

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_compatible_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_compatible" " using "
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

syntax (name := rr_posComboSuccDegree_rootCountAbove_nonRoot_of_countEq_named)
  "rr_posComboSuccDegree_rootCountAbove_nonRoot_of_countEq" " using "
    "count_eq" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCrossing_named)
  "rr_succDegree_pair_common_interleaver_rootCrossing" " using "
    "root_crossing" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCountAbove_named)
  "rr_succDegree_pair_common_interleaver_rootCountAbove" " using "
    "root_count_above" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_rootCountAboveNonRoot_named)
  "rr_succDegree_pair_common_interleaver_rootCountAboveNonRoot" " using "
    "root_count_above" ":=" term :
  tactic

syntax (name := rr_succDegree_pair_common_interleaver_closedSegmentCountEq_named)
  "rr_succDegree_pair_common_interleaver_closedSegmentCountEq" " using "
    "count_eq" ":=" term :
  tactic

syntax
  (name :=
    rr_succDegree_pair_common_interleaver_residualStrictInterl_bothNonzero_divXStrictInterl_named)
  "rr_succDegree_pair_common_interleaver_residualStrictInterl_\
    bothNonzero_divXStrictInterl" " using "
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
