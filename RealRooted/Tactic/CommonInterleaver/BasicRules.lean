import RealRooted.Tactic.CommonInterleaver.BasicSyntax

/-!
# Basic common-interleaver tactic rules

Macro expansions for compatibility transports, finite-family upgrades, and
their pointwise sequence forms.
-/

open Polynomial

namespace RealRooted
namespace Tactic

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
  | `(tactic| rr_compatible_sequence_comm using compatible := $h:term) =>
      `(tactic| exact RealRooted.compatible_sequence_comm $h)
  | `(tactic|
      rr_compatible_sequence_comp_X_add_C using
        compatible := $h:term,
        shift := $r:term) =>
      `(tactic| exact RealRooted.compatible_sequence_comp_X_add_C (c := $r) $h)
  | `(tactic|
      rr_compatible_sequence_reflect using
        compatible := $h:term,
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic| exact RealRooted.compatible_sequence_reflect $h $hfN $hgN)
  | `(tactic|
      rr_compatible_sequence_reflect_iff using
        left_degree_bound := $hfN:term,
        right_degree_bound := $hgN:term) =>
      `(tactic| exact RealRooted.compatible_sequence_reflect_iff $hfN $hgN)
  | `(tactic| rr_compatible_sequence_derivative using compatible := $h:term) =>
      `(tactic| exact RealRooted.compatible_sequence_derivative $h)
  | `(tactic|
      rr_compatible_sequence_left_realrooted using
        compatible := $h:term,
        left_pos_lc := $hfpos:term) =>
      `(tactic| exact RealRooted.compatible_sequence_left_realrooted $h $hfpos)
  | `(tactic|
      rr_compatible_sequence_right_realrooted using
        compatible := $h:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic| exact RealRooted.compatible_sequence_right_realrooted $h $hgpos)
  | `(tactic|
      rr_compatible_sequence_right_degree_le_succ using
        compatible := $h:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.compatible_sequence_right_degree_le_succ
          $h $hfpos $hgpos)
  | `(tactic|
      rr_compatible_sequence_degree_close using
        compatible := $h:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.compatible_sequence_degree_close $h $hfpos $hgpos)
  | `(tactic|
      rr_compatible_sequence_to_pos_combo using
        compatible := $h:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.compatible_sequence_to_pos_combo $h $hfpos $hgpos)
  | `(tactic|
      rr_compatible_sequence_of_pos_combo using
        pos_combo := $hfg:term,
        left_realrooted := $hf:term,
        right_realrooted := $hg:term) =>
      `(tactic| exact RealRooted.compatible_sequence_of_pos_combo $hfg $hf $hg)
  | `(tactic|
      rr_compatible_sequence_of_pos_combo_same_degree using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.compatible_sequence_of_pos_combo_same_degree
          $hfg $hfpos $hgpos $hdeg)
  | `(tactic|
      rr_compatible_sequence_of_pos_combo_succ_degree using
        pos_combo := $hfg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hdeg:term,
        left_splits := $hfsplits:term) =>
      `(tactic|
        exact RealRooted.compatible_sequence_of_pos_combo_succ_degree
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
      rr_compatible_sequence_of_common_left using
        common_to_left := $hhf:term,
        common_to_right := $hhg:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.compatible_sequence_of_common_left
          $hhf $hhg $hfpos $hgpos)
  | `(tactic|
      rr_compatible_sequence_of_common_right using
        left_to_common := $hfh:term,
        right_to_common := $hgh:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term) =>
      `(tactic|
        exact RealRooted.compatible_sequence_of_common_right
          $hfh $hgh $hfpos $hgpos)
  | `(tactic|
      rr_pos_combo_sequence_comp_X_add_C using
        pos_combo := $hfg:term,
        shift := $r:term) =>
      `(tactic| exact RealRooted.posCombo_sequence_comp_X_add_C (c := $r) $hfg)
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
  | `(tactic|
      rr_pairwise_compatible_sequence_of_common_left using
        common_left := $hcommon:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.pairwiseCompatible_sequence_of_commonLeftInterleaver
          $hcommon $hpos)
  | `(tactic|
      rr_pairwise_compatible_sequence_of_pairwise_common_left using
        pairwise_common_left := $hpair:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact
          RealRooted.pairwiseCompatible_sequence_of_pairwiseHasCommonLeftInterleaver
            $hpair $hpos)
  | `(tactic|
      rr_pairwise_compatible_sequence_of_common_right using
        common_right := $hcommon:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.pairwiseCompatible_sequence_of_commonInterleaver
          $hcommon $hpos)
  | `(tactic|
      rr_pairwise_compatible_sequence_of_pairwise_common_right using
        pairwise_common_right := $hpair:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact
          RealRooted.pairwiseCompatible_sequence_of_pairwiseHasCommonInterleaver
            $hpair $hpos)
  | `(tactic|
      rr_common_interleaver_sequence_of_pairwise using
        member_splits := $hrr:term,
        member_pos_lc := $hpos:term,
        pairwise_common := $hpair:term) =>
      `(tactic|
        exact RealRooted.hasCommonInterleaver_sequence_of_pairwiseHasCommonInterleaver
          $hrr $hpos $hpair)
  | `(tactic|
      rr_common_left_interleaver_sequence_of_pairwise using
        member_splits := $hrr:term,
        member_pos_lc := $hpos:term,
        pairwise_common_left := $hpair:term) =>
      `(tactic|
        exact
          RealRooted.hasCommonLeftInterleaver_sequence_of_pairwiseHasCommonLeftInterleaver
            $hrr $hpos $hpair)
  | `(tactic|
      rr_common_interleaver_sum_sequence_realrooted using
        common_right := $hcommon:term,
        member_pos_lc := $hpos:term,
        nonempty := $hne:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_sum_sequence_of_commonInterleaver
          $hcommon $hpos $hne)
  | `(tactic|
      rr_common_left_interleaver_sum_sequence_realrooted using
        common_left := $hcommon:term,
        member_pos_lc := $hpos:term,
        nonempty := $hne:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_sum_sequence_of_commonLeftInterleaver
          $hcommon $hpos $hne)

end Tactic
end RealRooted
