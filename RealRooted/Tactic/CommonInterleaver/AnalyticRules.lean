import RealRooted.Tactic.CommonInterleaver.AnalyticSyntax
import RealRooted.Tactic.CommonInterleaver.BasicRules

/-!
# Analytic common-interleaver tactic rules

Macro expansions for root-count certificates and two-polynomial
common-interleaver endpoints.
-/

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic| rr_sameDegree_rootCountAbove_nonRoot_analytic) =>
      `(tactic|
        exact
          RealRooted.posComboNoCommonSameDegreeRootCountAboveNonRootNonneg_from_analytic)
  | `(tactic| rr_sameDegree_pair_common_interleaver_analytic) =>
      `(tactic|
        exact
          RealRooted.PosComboNoCommonSameDegreePairHasCommonInterleaverNonneg)
  | `(tactic| rr_succDegree_pair_common_interleaver_local_lower) =>
      `(tactic|
        exact
          RealRooted.PosComboNoCommonSuccDegreePairHasCommonInterleaverNonneg)
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
  | `(tactic| rr_chudnovskySeymour_compatible_pair_common_interleaver_statement) =>
      `(tactic|
        exact RealRooted.chudnovskySeymour_compatiblePairHasCommonInterleaver)
  | `(tactic| rr_chudnovskySeymour_compatible_pair_common_left_interleaver_statement) =>
      `(tactic|
        exact RealRooted.chudnovskySeymour_compatiblePairHasCommonLeftInterleaver)
  | `(tactic|
      rr_chudnovskySeymour_compatible_pair_common_interleaver using
        left_pos_lc := $hf:term,
        right_pos_lc := $hg:term,
        compatible := $hcomp:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_chudnovskySeymour
          $hf $hg $hcomp)
  | `(tactic|
      rr_chudnovskySeymour_compatible_pair_common_left_interleaver using
        left_pos_lc := $hf:term,
        right_pos_lc := $hg:term,
        compatible := $hcomp:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonLeftInterleaver_chudnovskySeymour
          $hf $hg $hcomp)

end Tactic
end RealRooted
