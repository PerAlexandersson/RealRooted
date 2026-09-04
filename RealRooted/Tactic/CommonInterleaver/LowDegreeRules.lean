import RealRooted.Tactic.CommonInterleaver.FamilyRules
import RealRooted.Tactic.CommonInterleaver.LowDegreeSyntax

/-!
# Low-degree common-interleaver tactic rules

Macro expansions for degree-at-most-three pair and family endpoints.
-/

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
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
      rr_pair_common_interleaver_degree_le_one using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_degree_le_one := $hfdeg:term,
        right_degree_le_one := $hgdeg:term) =>
      `(tactic|
        exact RealRooted.pairHasCommonInterleaver_of_natDegree_le_one
          $hfpos $hgpos $hfdeg $hgdeg)
  | `(tactic|
      rr_pair_common_left_interleaver_degree_le_one using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_degree_le_one := $hfdeg:term,
        right_degree_le_one := $hgdeg:term) =>
      `(tactic|
        exact RealRooted.pairHasCommonLeftInterleaver_of_natDegree_le_one
          $hfpos $hgpos $hfdeg $hgdeg)
  | `(tactic|
      rr_pair_common_interleaver_sameDegree_degree_le_one using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term,
        left_degree_le_one := $hfdeg:term) =>
      `(tactic|
        exact RealRooted.pairHasCommonInterleaver_of_sameDegree_natDegree_le_one
          $hfpos $hgpos $hdeg $hfdeg)
  | `(tactic|
      rr_pair_common_left_interleaver_sameDegree_degree_le_one using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        same_degree := $hdeg:term,
        left_degree_le_one := $hfdeg:term) =>
      `(tactic|
        exact RealRooted.pairHasCommonLeftInterleaver_of_sameDegree_natDegree_le_one
          $hfpos $hgpos $hdeg $hfdeg)
  | `(tactic|
      rr_compatible_pair_common_interleaver_degree_le_one using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        compatible := $hfg:term,
        left_degree_le_one := $hfdeg:term,
        right_degree_le_one := $hgdeg:term) =>
      `(tactic|
        have _hfg := ($hfg);
        exact RealRooted.compatiblePairHasCommonInterleaver_of_natDegree_le_one
          $hfpos $hgpos $hfdeg $hgdeg)
  | `(tactic|
      rr_compatible_pair_common_left_interleaver_degree_le_one using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        compatible := $hfg:term,
        left_degree_le_one := $hfdeg:term,
        right_degree_le_one := $hgdeg:term) =>
      `(tactic|
        have _hfg := ($hfg);
        exact RealRooted.compatiblePairHasCommonLeftInterleaver_of_natDegree_le_one
          $hfpos $hgpos $hfdeg $hgdeg)
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
