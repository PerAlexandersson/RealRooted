import RealRooted.DegreeIncreasingLocalLowerCount
import RealRooted.RootContinuity
import RealRooted.RootCountJump
import RealRooted.SmallPositiveParameterCount
import RealRooted.SuccDegreeLeftEndpoint

/-!
# Root-count and continuity tactic frontends

Thin wrappers for public root-count and local-continuity endpoints used in
succ-degree positive-parameter arguments.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_natDegree_add_C_mul_lt_named)
  "rr_natDegree_add_C_mul_lt" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

syntax (name := rr_leadingCoeff_add_C_mul_lt_named)
  "rr_leadingCoeff_add_C_mul_lt" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

syntax (name := rr_exists_root_lt_succDegree_add_right_small_named)
  "rr_exists_root_lt_succDegree_add_right_small" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "bound" ":=" term :
  tactic

syntax (name := rr_degreeIncreasing_local_lower_count_named)
  "rr_degreeIncreasing_local_lower_count" " using "
    "left_splits" ":=" term ","
    "degree_lt" ":=" term ","
    "radius" ":=" term ","
    "radius_pos" ":=" term :
  tactic

syntax (name := rr_positiveParameter_local_lower_count_named)
  "rr_positiveParameter_local_lower_count" " using "
    "splits_on_interval" ":=" term ","
    "degree_on_interval" ":=" term ","
    "parameter_mem" ":=" term ","
    "radius_pos" ":=" term :
  tactic

syntax (name := rr_rightFamily_card_roots_gt_eq_local_lower_named)
  "rr_rightFamily_card_roots_gt_eq_local_lower" " using "
    "interval_order" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term ","
    "local_lower" ":=" term :
  tactic

syntax (name := rr_card_filter_gt_endpoint_eq_local_lower_named)
  "rr_card_filter_gt_endpoint_eq_local_lower" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term ","
    "threshold_not_left_root" ":=" term ","
    "small_local_lower" ":=" term ","
    "right_family_splits" ":=" term ","
    "right_family_not_root" ":=" term ","
    "swapped_family_splits" ":=" term ","
    "swapped_family_not_root" ":=" term :
  tactic

syntax (name := rr_closedSegment_eval_ne_zero_same_sign_named)
  "rr_closedSegment_eval_ne_zero_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_closedSegment_not_isRoot_same_sign_named)
  "rr_closedSegment_not_isRoot_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_rightFamily_eval_ne_zero_same_sign_named)
  "rr_rightFamily_eval_ne_zero_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

syntax (name := rr_exists_threshold_no_mem_Ioc_named)
  "rr_exists_threshold_no_mem_Ioc" :
  tactic

syntax (name := rr_exists_nonRoot_threshold_count_eq_named)
  "rr_exists_nonRoot_threshold_count_eq" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_exists_nonRoot_threshold_count_gt_eq_named)
  "rr_exists_nonRoot_threshold_count_gt_eq" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "threshold" ":=" term :
  tactic

syntax (name := rr_rootCount_diff_le_one_nonRoot_named)
  "rr_rootCount_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_abs_diff_le_one_nonRoot_named)
  "rr_rootCount_abs_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_diff_le_one_nonRoot_isRoot_named)
  "rr_rootCount_diff_le_one_nonRoot_isRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_named)
  "rr_rootCountAbove_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_isRoot_named)
  "rr_rootCountAbove_diff_le_one_nonRoot_isRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

syntax (name := rr_rootCount_max_abs_diff_le_one_named)
  "rr_rootCount_max_abs_diff_le_one" " using "
    "bundled_bound" ":=" term :
  tactic

syntax (name := rr_left_card_roots_succDegree_named)
  "rr_left_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_right_card_roots_succDegree_named)
  "rr_right_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_left_ne_zero_card_roots_succDegree_named)
  "rr_left_ne_zero_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_right_ne_zero_card_roots_succDegree_named)
  "rr_right_ne_zero_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_mono_named)
  "rr_card_roots_filter_le_mono" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_antitone_named)
  "rr_card_roots_filter_gt_antitone" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_mono_named)
  "rr_card_roots_filter_le_and_gt_mono" " using "
    "interval_order" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_natDegree_add_C_mul_lt using
        parameter_ne_zero := $hμ:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact Polynomial.natDegree_add_C_mul_of_natDegree_lt $hμ $hdeg)
  | `(tactic|
      rr_leadingCoeff_add_C_mul_lt using
        parameter_ne_zero := $hμ:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt $hμ $hdeg)
  | `(tactic|
      rr_exists_root_lt_succDegree_add_right_small using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hdeg:term,
        bound := $A:term) =>
      `(tactic|
        exact RealRooted.exists_root_lt_of_succDegree_add_right_small
          $hfpos $hgpos $hdeg $A)
  | `(tactic|
      rr_degreeIncreasing_local_lower_count using
        left_splits := $hf:term,
        degree_lt := $hdeg:term,
        radius := $ρ:term,
        radius_pos := $hρ:term) =>
      `(tactic|
        exact RealRooted.degreeIncreasing_local_lower_count
          $hf $hdeg $ρ $hρ)
  | `(tactic|
      rr_positiveParameter_local_lower_count using
        splits_on_interval := $hsplit:term,
        degree_on_interval := $hdeg:term,
        parameter_mem := $hμ:term,
        radius_pos := $hρ:term) =>
      `(tactic|
        exact RealRooted.positiveParameter_local_lower_count
          $hsplit $hdeg $hμ $hρ)
  | `(tactic|
      rr_rightFamily_card_roots_gt_eq_local_lower using
        interval_order := $hμ₁:term,
        degree_on_interval := $hdeg:term,
        splits_on_interval := $hrr:term,
        threshold_not_root := $hne:term,
        local_lower := $hlower:term) =>
      `(tactic|
        exact RealRooted.rightFamily_card_roots_gt_eq_of_local_lower_counts
          $hμ₁ $hdeg $hrr $hne $hlower)
  | `(tactic|
      rr_card_filter_gt_endpoint_eq_local_lower using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hdeg:term,
        left_splits := $hfsplit:term,
        threshold_not_left_root := $hx:term,
        small_local_lower := $hlocal:term,
        right_family_splits := $hfgsplit:term,
        right_family_not_root := $hfgno:term,
        swapped_family_splits := $hgfsplit:term,
        swapped_family_not_root := $hgfno:term) =>
      `(tactic|
        exact RealRooted.card_filter_gt_endpoint_eq_of_local_lower_counts
          $hfpos $hgpos $hdeg $hfsplit $hx $hlocal $hfgsplit $hfgno
          $hgfsplit $hgfno)
  | `(tactic|
      rr_closedSegment_eval_ne_zero_same_sign using
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term,
        eval_product_pos := $hprod:term) =>
      `(tactic|
        exact RealRooted.closedSegment_eval_ne_zero_of_eval_mul_pos
          $hβ0 $hβ1 $hprod)
  | `(tactic|
      rr_closedSegment_not_isRoot_same_sign using
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term,
        eval_product_pos := $hprod:term) =>
      `(tactic|
        exact RealRooted.closedSegment_not_isRoot_of_eval_mul_pos
          $hβ0 $hβ1 $hprod)
  | `(tactic|
      rr_rightFamily_eval_ne_zero_same_sign using
        parameter_nonneg := $hμ:term,
        eval_product_pos := $hprod:term) =>
      `(tactic|
        exact RealRooted.rightFamily_eval_ne_zero_of_eval_mul_pos $hμ $hprod)
  | `(tactic| rr_exists_threshold_no_mem_Ioc) =>
      `(tactic| exact RealRooted.exists_threshold_no_mem_Ioc _ _)
  | `(tactic|
      rr_exists_nonRoot_threshold_count_eq using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        threshold := $x:term) =>
      `(tactic| exact RealRooted.exists_nonRoot_threshold_count_eq $hf $hg $x)
  | `(tactic|
      rr_exists_nonRoot_threshold_count_gt_eq using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        threshold := $x:term) =>
      `(tactic| exact RealRooted.exists_nonRoot_threshold_count_gt_eq $hf $hg $x)
  | `(tactic|
      rr_rootCount_diff_le_one_nonRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCount_diff_le_one_of_nonRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_abs_diff_le_one_nonRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCount_abs_diff_le_one_of_nonRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_diff_le_one_nonRoot_isRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCount_diff_le_one_of_nonRoot_isRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCountAbove_diff_le_one_nonRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCountAbove_diff_le_one_of_nonRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCountAbove_diff_le_one_nonRoot_isRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCountAbove_diff_le_one_of_nonRoot_isRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_max_abs_diff_le_one using
        bundled_bound := $h:term) =>
      `(tactic| exact RealRooted.rootCount_max_abs_diff_le_one_of_bundled $h)
  | `(tactic|
      rr_left_card_roots_succDegree using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.left_card_roots_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_right_card_roots_succDegree using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.right_card_roots_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_left_ne_zero_card_roots_succDegree using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.left_ne_zero_and_card_roots_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_right_ne_zero_card_roots_succDegree using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.right_ne_zero_and_card_roots_of_succDegree
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_card_roots_filter_le_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_eq_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_gt_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_eq_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_all_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_all_eq_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_le_mono using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_mono_of_le $hab)
  | `(tactic|
      rr_card_roots_filter_gt_antitone using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_antitone_of_le $hab)
  | `(tactic|
      rr_card_roots_filter_le_and_gt_mono using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_and_gt_mono_of_le $hab)
  | `(tactic|
      rr_card_roots_filter_le_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_eq_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_gt_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_eq_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_Ioc_zero_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_Ioc_eq_zero_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_all_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_all_eq_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_sub_eq_of_no_isRoot_Ioc
          $hab $hf $hg)
  | `(tactic|
      rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc
          $hab $hf $hg)
  | `(tactic|
      rr_card_roots_filter_le_bound_no_isRoot_Ioc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_bound_of_no_isRoot_Ioc
          $hab $hf $hg $h)
  | `(tactic|
      rr_card_roots_filter_gt_bound_no_isRoot_Ioc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_bound_of_no_isRoot_Ioc
          $hab $hf $hg $h)
  | `(tactic|
      rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        lower_source_bound := $hle:term,
        upper_source_bound := $hgt:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_and_gt_bound_of_no_isRoot_Ioc
          $hab $hf $hg $hle $hgt)
  | `(tactic|
      rr_card_roots_filter_le_sub_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_sub_eq_of_no_isRoot_Icc
          $hab $hf $hg)
  | `(tactic|
      rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_sub_eq_of_no_isRoot_Icc
          $hab $hf $hg)
  | `(tactic|
      rr_card_roots_filter_le_bound_no_isRoot_Icc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_bound_of_no_isRoot_Icc
          $hab $hf $hg $h)
  | `(tactic|
      rr_card_roots_filter_gt_bound_no_isRoot_Icc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_bound_of_no_isRoot_Icc
          $hab $hf $hg $h)
  | `(tactic|
      rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        lower_source_bound := $hle:term,
        upper_source_bound := $hgt:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_and_gt_bound_of_no_isRoot_Icc
          $hab $hf $hg $hle $hgt)

end Tactic
end RealRooted
