import RealRooted.Tactic.RootCount.CoreRules
import RealRooted.Tactic.RootCount.LowDegreeSyntax

/-!
# Low-degree root-count tactic rules

Macro expansions for same-degree and low-degree root-count certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_rightFamily_sameDegree_gt_count_eq using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        left_parameter_nonneg := $hμ₀:term,
        interval_order := $hμ₀μ₁:term,
        threshold_not_root := $hne:term) =>
      `(tactic|
        exact RealRooted.rightFamily_card_roots_gt_eq_of_no_isRoot_interval_sameDegree
          $hfpos $hgpos $hfg $hdeg $hμ₀ $hμ₀μ₁ $hne)
  | `(tactic|
      rr_rightFamily_sameDegree_gt_count_eq_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        left_parameter_nonneg := $hμ₀:term,
        interval_order := $hμ₀μ₁:term,
        threshold_not_root := $hne:term) =>
      `(tactic|
        exact RealRooted.Tactic.rightFamily_sameDegree_gt_count_eq_sequence
          $hfpos $hgpos $hfg $hdeg $hμ₀ $hμ₀μ₁ $hne)
  | `(tactic|
      rr_rightFamily_zero_one_gt_count_eq using
        degree_on_interval := $hdeg:term,
        splits_on_interval := $hrr:term,
        threshold_not_root := $hne:term) =>
      `(tactic|
        exact RealRooted.rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
          $hdeg $hrr $hne)
  | `(tactic|
      rr_rightFamily_zero_one_gt_count_eq_sequence using
        degree_on_interval := $hdeg:term,
        splits_on_interval := $hrr:term,
        threshold_not_root := $hne:term) =>
      `(tactic|
        exact RealRooted.Tactic.rightFamily_zero_one_gt_count_eq_sequence
          $hdeg $hrr $hne)
  | `(tactic|
      rr_sameDegree_gt_count_eq_no_rightFamily using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        right_not_root := $hxg:term,
        no_right_family_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.sameDegree_card_roots_gt_eq_of_no_rightFamily_isRoot
          $hfpos $hgpos $hfg $hdeg $hxg $hno)
  | `(tactic|
      rr_sameDegree_gt_count_eq_no_rightFamily_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        right_not_root := $hxg:term,
        no_right_family_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.Tactic.sameDegree_gt_count_eq_no_rightFamily_sequence
          $hfpos $hgpos $hfg $hdeg $hxg $hno)
  | `(tactic|
      rr_sameDegree_rootCountAbove_no_rightFamily using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        right_not_root := $hxg:term,
        no_right_family_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.sameDegree_rootCountAbove_pointwise_of_no_rightFamily_isRoot
          $hfpos $hgpos $hfg $hdeg $hxg $hno)
  | `(tactic|
      rr_sameDegree_rootCountAbove_no_rightFamily_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        right_not_root := $hxg:term,
        no_right_family_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.sameDegree_rootCountAbove_no_rightFamily_sequence
            $hfpos $hgpos $hfg $hdeg $hxg $hno)
  | `(tactic|
      rr_sameDegree_rootCountAbove_no_pos_crossing using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        left_not_root := $hxf:term,
        right_not_root := $hxg:term,
        no_positive_crossing := $hno:term) =>
      `(tactic|
        exact RealRooted.sameDegree_rootCountAbove_pointwise_of_not_exists_pos_isRoot
          $hfpos $hgpos $hfg $hdeg $hxf $hxg $hno)
  | `(tactic|
      rr_sameDegree_rootCountAbove_no_pos_crossing_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        left_not_root := $hxf:term,
        right_not_root := $hxg:term,
        no_positive_crossing := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.sameDegree_rootCountAbove_no_pos_crossing_sequence
            $hfpos $hgpos $hfg $hdeg $hxf $hxg $hno)
  | `(tactic|
      rr_sameDegree_rootCountAbove_pos_crossing using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_not_root := $hxf:term,
        right_not_root := $hxg:term,
        positive_crossing := $hcross:term) =>
      `(tactic|
        exact RealRooted.sameDegree_rootCountAbove_pointwise_of_exists_pos_isRoot
          $hfpos $hgpos $hfg $hdeg $hno $hxf $hxg $hcross)
  | `(tactic|
      rr_sameDegree_rootCountAbove_pos_crossing_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_not_root := $hxf:term,
        right_not_root := $hxg:term,
        positive_crossing := $hcross:term) =>
      `(tactic|
        exact RealRooted.Tactic.sameDegree_rootCountAbove_pos_crossing_sequence
          $hfpos $hgpos $hfg $hdeg $hno $hxf $hxg $hcross)
  | `(tactic|
      rr_posCombo_sameDegree_rootCount_degree_le_two using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_two := $hfdeg:term,
        threshold := $x:term) =>
      `(tactic|
        exact rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
          $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg $x)
  | `(tactic|
      rr_posCombo_sameDegree_rootCount_degree_le_two_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_two := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCount_degree_le_two_sequence
            $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCountAbove_degree_le_two using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_two := $hfdeg:term,
        threshold := $x:term) =>
      `(tactic|
        exact rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
          $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg $x)
  | `(tactic|
      rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_two := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCountAbove_degree_le_two_sequence
            $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_sameDegree_rootCrossing_degree_le_one using
        left_degree_le_one := $hfdeg:term) =>
      `(tactic|
        exact sameDegreeRootCrossing_of_natDegree_le_one $hfdeg)
  | `(tactic|
      rr_sameDegree_rootCrossing_degree_le_one_sequence using
        left_degree_le_one := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.sameDegree_rootCrossing_degree_le_one_sequence
            $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCrossing_degree_le_two using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_two := $hfdeg:term) =>
      `(tactic|
        exact sameDegreeRootCrossing_of_posCombo_natDegree_le_two
          $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_two := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCrossing_degree_le_two_sequence
            $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCount_degree_le_three using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term,
        threshold := $x:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sameDegree_rootCount_degree_le_three
          $x $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCount_degree_le_three_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCount_degree_le_three_sequence
            $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCountAbove_degree_le_three using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term,
        threshold := $x:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sameDegree_rootCountAbove_degree_le_three
          $x $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCountAbove_degree_le_three_sequence
            $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCrossing_degree_le_three using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.posCombo_sameDegree_rootCrossing_degree_le_three
          $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCrossing_degree_le_three_sequence
            $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno $hfdeg)
  | `(tactic|
      rr_compatible_succDegree_rootCountAbove_le_two using
        compatible := $hcomp:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hdeg:term,
        left_splits := $hfsplit:term,
        left_degree_le_two := $hfdeg:term,
        threshold := $x:term) =>
      `(tactic|
        exact compatibleSuccDegreeRootCountAbove_le_two_of_natDegree_le_two
          $hcomp $hfpos $hgpos $hdeg $hfsplit $hfdeg $x)
  | `(tactic|
      rr_compatible_succDegree_rootCountAbove_le_two_sequence using
        compatible := $hcomp:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hdeg:term,
        left_splits := $hfsplit:term,
        left_degree_le_two := $hfdeg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.compatible_succDegree_rootCountAbove_le_two_sequence
            $hcomp $hfpos $hgpos $hdeg $hfsplit $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCount_cubicInterior using
        below_certificate := $hbelow:term,
        above_certificate := $habove:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term,
        threshold := $x:term) =>
      `(tactic|
        exact
          rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
            $hbelow $habove $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno
            $hfdeg $x)
  | `(tactic|
      rr_posCombo_sameDegree_rootCount_cubicInterior_sequence using
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
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCount_cubicInterior_sequence
            $hbelow $habove $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno
            $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCountAbove_cubicInterior using
        below_certificate := $hbelow:term,
        above_certificate := $habove:term,
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        left_nonneg_coeffs := $hfnn:term,
        right_nonneg_coeffs := $hgnn:term,
        pos_combo := $hfg:term,
        same_degree := $hdeg:term,
        no_common_roots := $hno:term,
        left_degree_le_three := $hfdeg:term,
        threshold := $x:term) =>
      `(tactic|
        exact
          rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
            $hbelow $habove $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno
            $hfdeg $x)
  | `(tactic|
      rr_posCombo_sameDegree_rootCountAbove_cubicInterior_sequence using
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
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCountAbove_cubicInterior_sequence
            $hbelow $habove $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno
            $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCrossing_cubicInterior using
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
        exact
          sameDegreeRootCrossing_of_posCombo_natDegree_le_three_of_cubicInterior
            $hbelow $habove $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno
            $hfdeg)
  | `(tactic|
      rr_posCombo_sameDegree_rootCrossing_cubicInterior_sequence using
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
        exact
          RealRooted.Tactic.posCombo_sameDegree_rootCrossing_cubicInterior_sequence
            $hbelow $habove $hfpos $hgpos $hfnn $hgnn $hfg $hdeg $hno
            $hfdeg)

end Tactic
end RealRooted
