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
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_compatible using
        root_count := $hcount:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
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
  | `(tactic|
      rr_posComboSuccDegree_rootCountAbove_nonRoot_of_countEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCrossing using
        root_crossing := $hcross:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing
          $hcross)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCountAbove using
        root_count_above := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_rootCountAboveNonRoot using
        root_count_above := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_nonRoot
          $hcount)
  | `(tactic|
      rr_succDegree_pair_common_interleaver_closedSegmentCountEq using
        count_eq := $hcount:term) =>
      `(tactic|
        exact RealRooted.succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq
          $hcount)
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
