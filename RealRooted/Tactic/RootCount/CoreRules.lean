import RealRooted.Tactic.Lookup
import RealRooted.Tactic.RootCount.CoreSyntax
import RealRooted.Tactic.SideGoals

/-!
# Core root-count tactic rules

Macro expansions for general root-count and local-continuity certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_natDegree_add_C_mul_lt using
        parameter_ne_zero := $hμ:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact Polynomial.natDegree_add_C_mul_of_natDegree_lt $hμ $hdeg)
  | `(tactic|
      rr_natDegree_add_C_mul_lt_sequence using
        parameter_ne_zero := $hμ:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.natDegree_add_C_mul_lt_sequence $hμ $hdeg)
  | `(tactic|
      rr_leadingCoeff_add_C_mul_lt using
        parameter_ne_zero := $hμ:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt $hμ $hdeg)
  | `(tactic|
      rr_leadingCoeff_add_C_mul_lt_sequence using
        parameter_ne_zero := $hμ:term,
        degree_lt := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.leadingCoeff_add_C_mul_lt_sequence $hμ $hdeg)
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
      rr_exists_root_lt_succDegree_add_right_small_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        succ_degree := $hdeg:term,
        bound := $A:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.exists_root_lt_succDegree_add_right_small_sequence
            $A $hfpos $hgpos $hdeg)
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
      rr_degreeIncreasing_local_lower_count_sequence using
        left_splits := $hf:term,
        degree_lt := $hdeg:term,
        radius := $ρ:term,
        radius_pos := $hρ:term) =>
      `(tactic|
        exact RealRooted.Tactic.degreeIncreasing_local_lower_count_sequence
          $ρ $hf $hdeg $hρ)
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
      rr_positiveParameter_local_lower_count_sequence using
        splits_on_interval := $hsplit:term,
        degree_on_interval := $hdeg:term,
        parameter_mem := $hμ:term,
        radius_pos := $hρ:term) =>
      `(tactic|
        exact RealRooted.Tactic.positiveParameter_local_lower_count_sequence
          $hsplit $hdeg $hμ $hρ)
  | `(tactic|
      rr_rightFamily_card_roots_gt_eq_zero_param using
        parameter_pos := $hμ:term,
        degree_on_interval := $hdeg:term,
        splits_on_interval := $hsplit:term,
        threshold_not_root := $hne:term) =>
      `(tactic|
        exact
          RealRooted.rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
            $hμ $hdeg $hsplit $hne)
  | `(tactic| rr_rightFamily_card_roots_gt_eq_zero_param) =>
      `(tactic|
        rr_refine_then
          (RealRooted.rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
            ?_ ?_ ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_rightFamily_card_roots_gt_eq_zero_param_sequence using
        parameter_pos := $hμ:term,
        degree_on_interval := $hdeg:term,
        splits_on_interval := $hsplit:term,
        threshold_not_root := $hne:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.rightFamily_card_roots_gt_eq_zero_param_sequence
            $hμ $hdeg $hsplit $hne)
  | `(tactic| rr_rightFamily_card_roots_gt_eq_zero_param_sequence) =>
      `(tactic|
        rr_refine_then
          (RealRooted.Tactic.rightFamily_card_roots_gt_eq_zero_param_sequence
            ?_ ?_ ?_ ?_)
          with rr_lookup)
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
      rr_rightFamily_card_roots_gt_eq_local_lower_sequence using
        interval_order := $hμ₁:term,
        degree_on_interval := $hdeg:term,
        splits_on_interval := $hrr:term,
        threshold_not_root := $hne:term,
        local_lower := $hlower:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.rightFamily_card_roots_gt_eq_local_lower_sequence
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
      rr_card_filter_gt_endpoint_eq_local_lower_sequence using
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
        exact RealRooted.Tactic.card_filter_gt_endpoint_eq_local_lower_sequence
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
      rr_closedSegment_eval_ne_zero_same_sign_sequence using
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term,
        eval_product_pos := $hprod:term) =>
      `(tactic|
        exact RealRooted.Tactic.closedSegment_eval_ne_zero_same_sign_sequence
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
      rr_closedSegment_not_isRoot_same_sign_sequence using
        parameter_nonneg := $hβ0:term,
        parameter_le_one := $hβ1:term,
        eval_product_pos := $hprod:term) =>
      `(tactic|
        exact RealRooted.Tactic.closedSegment_not_isRoot_same_sign_sequence
          $hβ0 $hβ1 $hprod)
  | `(tactic|
      rr_rightFamily_eval_ne_zero_same_sign using
        parameter_nonneg := $hμ:term,
        eval_product_pos := $hprod:term) =>
      `(tactic|
        exact RealRooted.rightFamily_eval_ne_zero_of_eval_mul_pos $hμ $hprod)
  | `(tactic|
      rr_rightFamily_eval_ne_zero_same_sign_sequence using
        parameter_nonneg := $hμ:term,
        eval_product_pos := $hprod:term) =>
      `(tactic|
        exact RealRooted.Tactic.rightFamily_eval_ne_zero_same_sign_sequence
          $hμ $hprod)
  | `(tactic| rr_exists_threshold_no_mem_Ioc) =>
      `(tactic| exact RealRooted.exists_threshold_no_mem_Ioc _ _)
  | `(tactic| rr_exists_threshold_no_mem_Ioc_sequence) =>
      `(tactic| exact RealRooted.Tactic.exists_threshold_no_mem_Ioc_sequence _ _)
  | `(tactic|
      rr_exists_nonRoot_threshold_count_eq using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        threshold := $x:term) =>
      `(tactic| exact RealRooted.exists_nonRoot_threshold_count_eq $hf $hg $x)
  | `(tactic|
      rr_exists_nonRoot_threshold_count_eq_sequence using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term) =>
      `(tactic|
        exact RealRooted.Tactic.exists_nonRoot_threshold_count_eq_sequence
          $hf $hg)
  | `(tactic|
      rr_exists_nonRoot_threshold_count_gt_eq using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        threshold := $x:term) =>
      `(tactic| exact RealRooted.exists_nonRoot_threshold_count_gt_eq $hf $hg $x)
  | `(tactic|
      rr_exists_nonRoot_threshold_count_gt_eq_sequence using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term) =>
      `(tactic|
        exact RealRooted.Tactic.exists_nonRoot_threshold_count_gt_eq_sequence
          $hf $hg)
  | `(tactic|
      rr_rootCount_diff_le_one_nonRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCount_diff_le_one_of_nonRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_diff_le_one_nonRoot_sequence using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic|
        exact RealRooted.Tactic.rootCount_diff_le_one_nonRoot_sequence
          $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_abs_diff_le_one_nonRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCount_abs_diff_le_one_of_nonRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_abs_diff_le_one_nonRoot_sequence using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic|
        exact RealRooted.Tactic.rootCount_abs_diff_le_one_nonRoot_sequence
          $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_diff_le_one_nonRoot_isRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCount_diff_le_one_of_nonRoot_isRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_diff_le_one_nonRoot_isRoot_sequence using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic|
        exact RealRooted.Tactic.rootCount_diff_le_one_nonRoot_isRoot_sequence
          $hf $hg $hbound)
  | `(tactic|
      rr_rootCountAbove_diff_le_one_nonRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCountAbove_diff_le_one_of_nonRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCountAbove_diff_le_one_nonRoot_sequence using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic|
        exact RealRooted.Tactic.rootCountAbove_diff_le_one_nonRoot_sequence
          $hf $hg $hbound)
  | `(tactic|
      rr_rootCountAbove_diff_le_one_nonRoot_isRoot using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic| exact RealRooted.rootCountAbove_diff_le_one_of_nonRoot_isRoot
        $hf $hg $hbound)
  | `(tactic|
      rr_rootCountAbove_diff_le_one_nonRoot_isRoot_sequence using
        left_ne_zero := $hf:term,
        right_ne_zero := $hg:term,
        nonroot_bound := $hbound:term) =>
      `(tactic|
        exact RealRooted.Tactic.rootCountAbove_diff_le_one_nonRoot_isRoot_sequence
          $hf $hg $hbound)
  | `(tactic|
      rr_rootCount_max_abs_diff_le_one using
        bundled_bound := $h:term) =>
      `(tactic| exact RealRooted.rootCount_max_abs_diff_le_one_of_bundled $h)
  | `(tactic|
      rr_rootCount_max_abs_diff_le_one_sequence using
        bundled_bound := $h:term) =>
      `(tactic|
        exact RealRooted.Tactic.rootCount_max_abs_diff_le_one_sequence $h)
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
      rr_left_card_roots_succDegree_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.Tactic.left_card_roots_succDegree_sequence
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
      rr_right_card_roots_succDegree_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.Tactic.right_card_roots_succDegree_sequence
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
      rr_left_ne_zero_card_roots_succDegree_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.Tactic.left_ne_zero_card_roots_succDegree_sequence
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
      rr_right_ne_zero_card_roots_succDegree_sequence using
        left_pos_lc := $hfpos:term,
        right_pos_lc := $hgpos:term,
        pos_combo := $hfg:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact RealRooted.Tactic.right_ne_zero_card_roots_succDegree_sequence
          $hfpos $hgpos $hfg $hsucc)
  | `(tactic|
      rr_card_roots_filter_le_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_eq_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_le_eq_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_eq_no_isRoot_Ioc_sequence
            $hab $hno)
  | `(tactic|
      rr_card_roots_filter_gt_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_eq_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_gt_eq_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_gt_eq_no_isRoot_Ioc_sequence
            $hab $hno)
  | `(tactic|
      rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence
            $hab $hno)
  | `(tactic|
      rr_card_roots_filter_all_eq_no_isRoot_Ioc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_all_eq_of_no_isRoot_Ioc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_all_eq_no_isRoot_Ioc_sequence
            $hab $hno)
  | `(tactic|
      rr_card_roots_filter_le_mono using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_mono_of_le $hab)
  | `(tactic|
      rr_card_roots_filter_le_mono_sequence using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.Tactic.card_roots_filter_le_mono_sequence $hab)
  | `(tactic|
      rr_card_roots_filter_gt_antitone using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_antitone_of_le $hab)
  | `(tactic|
      rr_card_roots_filter_gt_antitone_sequence using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.Tactic.card_roots_filter_gt_antitone_sequence $hab)
  | `(tactic|
      rr_card_roots_filter_le_and_gt_mono using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_and_gt_mono_of_le $hab)
  | `(tactic|
      rr_card_roots_filter_le_and_gt_mono_sequence using
        interval_order := $hab:term) =>
      `(tactic|
        exact RealRooted.Tactic.card_roots_filter_le_and_gt_mono_sequence $hab)
  | `(tactic|
      rr_card_roots_filter_le_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_le_eq_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_le_eq_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_eq_no_isRoot_Icc_sequence
            $hab $hno)
  | `(tactic|
      rr_card_roots_filter_gt_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_gt_eq_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_gt_eq_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_gt_eq_no_isRoot_Icc_sequence
            $hab $hno)
  | `(tactic|
      rr_card_roots_filter_Ioc_zero_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_Ioc_eq_zero_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence
            $hab $hno)
  | `(tactic|
      rr_card_roots_filter_all_eq_no_isRoot_Icc using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.card_roots_filter_all_eq_of_no_isRoot_Icc
          $hab $hno)
  | `(tactic|
      rr_card_roots_filter_all_eq_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        no_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_all_eq_no_isRoot_Icc_sequence
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
      rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence
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
      rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence
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
      rr_card_roots_filter_le_bound_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_bound_no_isRoot_Ioc_sequence
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
      rr_card_roots_filter_gt_bound_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_gt_bound_no_isRoot_Ioc_sequence
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
      rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        lower_source_bound := $hle:term,
        upper_source_bound := $hgt:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence
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
      rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence
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
      rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence
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
      rr_card_roots_filter_le_bound_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_bound_no_isRoot_Icc_sequence
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
      rr_card_roots_filter_gt_bound_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        source_bound := $h:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_gt_bound_no_isRoot_Icc_sequence
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
  | `(tactic|
      rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence using
        interval_order := $hab:term,
        left_no_roots := $hf:term,
        right_no_roots := $hg:term,
        lower_source_bound := $hle:term,
        upper_source_bound := $hgt:term) =>
      `(tactic|
        exact
          RealRooted.Tactic.card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence
            $hab $hf $hg $hle $hgt)

end Tactic
end RealRooted
