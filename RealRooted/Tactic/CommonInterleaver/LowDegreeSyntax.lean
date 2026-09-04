import RealRooted.Tactic.CommonInterleaver.FamilySyntax

/-!
# Low-degree common-interleaver tactic syntax

Parser declarations for degree-at-most-three pair and family endpoints.
-/

namespace RealRooted
namespace Tactic

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

syntax (name := rr_pair_common_interleaver_degree_le_one_named)
  "rr_pair_common_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pair_common_left_interleaver_degree_le_one_named)
  "rr_pair_common_left_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pair_common_interleaver_sameDegree_degree_le_one_named)
  "rr_pair_common_interleaver_sameDegree_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_one" ":=" term :
  tactic

syntax (name := rr_pair_common_left_interleaver_sameDegree_degree_le_one_named)
  "rr_pair_common_left_interleaver_sameDegree_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_one" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_interleaver_degree_le_one_named)
  "rr_compatible_pair_common_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
  tactic

syntax (name := rr_compatible_pair_common_left_interleaver_degree_le_one_named)
  "rr_compatible_pair_common_left_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
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

end Tactic
end RealRooted
