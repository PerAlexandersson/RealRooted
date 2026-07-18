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

syntax (name := rr_compatible_pair_common_interleaver_degree_split_nonnegShift_named)
  "rr_compatible_pair_common_interleaver_degree_split_nonnegShift" " using "
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
      rr_compatible_pair_common_interleaver_degree_split_nonnegShift using
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
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

end Tactic
end RealRooted
