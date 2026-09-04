import RealRooted.Tactic.CommonInterleaver.AnalyticSyntax

/-!
# Family common-interleaver tactic syntax

Parser declarations for Chudnovsky--Seymour four-way certificates and
pairwise-to-family compatibility upgrades.
-/

namespace RealRooted
namespace Tactic

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

syntax (name := rr_chudnovskySeymour_fourWay_degreeSplit_nonnegShift_named)
  "rr_chudnovskySeymour_fourWay_degreeSplit_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_slotData_nonnegShift_named)
  "rr_chudnovskySeymour_fourWay_slotData_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_affineFamily_nonnegShift_named)
  "rr_chudnovskySeymour_fourWay_affineFamily_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_boundaryRight_nonnegShift_named)
  "rr_chudnovskySeymour_fourWay_boundaryRight_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "boundary_right" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_sameDegreePair_affineFamily_nonneg_named)
  "rr_chudnovskySeymour_fourWay_sameDegreePair_affineFamily_nonneg" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_allCombo_nonnegCoeffs_named)
  "rr_chudnovskySeymour_fourWay_allCombo_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_affineFamily_nonnegCoeffs_named)
  "rr_chudnovskySeymour_fourWay_affineFamily_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_boundaryRight_nonnegCoeffs_named)
  "rr_chudnovskySeymour_fourWay_boundaryRight_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "boundary_right" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_posComboBridge_named)
  "rr_chudnovskySeymour_fourWay_posComboBridge" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pos_combo_bridge" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_noCommonOrientation_degreeClose_named)
  "rr_chudnovskySeymour_fourWay_noCommonOrientation_degreeClose" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "orientation" ":=" term ","
    "degree_close" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_noCommonOrientation_nonnegCoeffs_named)
  "rr_chudnovskySeymour_fourWay_noCommonOrientation_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "orientation" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_pairDegreeSplit_nonnegCoeffs_named)
  "rr_chudnovskySeymour_fourWay_pairDegreeSplit_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_degreeSplit_nonnegCoeffs_named)
  "rr_chudnovskySeymour_fourWay_degreeSplit_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_degree_le_one_named)
  "rr_chudnovskySeymour_fourWay_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_degree_le_two_named)
  "rr_chudnovskySeymour_fourWay_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
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

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegShift_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_slotData_nonnegShift_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_slotData_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegShift_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegShift_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "boundary_right" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_commonInterleaver_sameDegreePair_affineFamily_nonneg_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_sameDegreePair_affineFamily_nonneg"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_allCombo_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_allCombo_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_affineFamily_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_boundaryRight_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "boundary_right" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_posComboBridge_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_posComboBridge" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pos_combo_bridge" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_degreeClose_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_degreeClose"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "orientation" ":=" term ","
    "degree_close" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_noCommonOrientation_nonnegCoeffs"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "orientation" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_commonInterleaver_pairDegreeSplit_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_pairDegreeSplit_nonnegCoeffs"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_degreeSplit_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_named)
  "rr_chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_named)
  "rr_chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_named)
  "rr_chudnovskySeymour_pairwiseCompatible_iff_familyCompatible" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term :
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

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegShift_named)
  "rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_slotData_nonnegShift_named)
  "rr_pairwiseCompatible_iff_familyCompatible_slotData_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegShift_named)
  "rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegShift_named)
  "rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegShift" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "boundary_right" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_familyCompatible_sameDegreePair_affineFamily_nonneg_named)
  "rr_pairwiseCompatible_iff_familyCompatible_sameDegreePair_affineFamily_nonneg"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_allCombo_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_familyCompatible_allCombo_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "all_combo" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_familyCompatible_affineFamily_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "affine_family" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_familyCompatible_boundaryRight_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "boundary_right" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_posComboBridge_named)
  "rr_pairwiseCompatible_iff_familyCompatible_posComboBridge" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pos_combo_bridge" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_degreeClose_named)
  "rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_degreeClose"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "orientation" ":=" term ","
    "degree_close" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_familyCompatible_noCommonOrientation_nonnegCoeffs"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "orientation" ":=" term :
  tactic

syntax
  (name := rr_pairwiseCompatible_iff_familyCompatible_pairDegreeSplit_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_familyCompatible_pairDegreeSplit_nonnegCoeffs"
    " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegCoeffs_named)
  "rr_pairwiseCompatible_iff_familyCompatible_degreeSplit_nonnegCoeffs" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_nonneg_coeffs" ":=" term ","
    "same_degree" ":=" term ","
    "succ_degree" ":=" term :
  tactic

end Tactic
end RealRooted
