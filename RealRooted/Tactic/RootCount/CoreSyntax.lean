module

public import RealRooted.Tactic.RootCount.SequenceCore

/-!
# Core root-count tactic syntax

Parser declarations for general root-count and local-continuity certificates.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `(f + C a * g).natDegree = g.natDegree` from `parameter_ne_zero : a ≠ 0` and
`degree_lt : f.natDegree < g.natDegree`. -/
syntax (name := rr_natDegree_add_C_mul_lt_named)
  "rr_natDegree_add_C_mul_lt" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

/-- Sequence form of `rr_natDegree_add_C_mul_lt`: the same certificate for every index `i : Nat`. -/
syntax (name := rr_natDegree_add_C_mul_lt_sequence_named)
  "rr_natDegree_add_C_mul_lt_sequence" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

/-- Closes `(f + C a * g).leadingCoeff = a * g.leadingCoeff` from `parameter_ne_zero : a ≠ 0` and
`degree_lt : f.natDegree < g.natDegree`. -/
syntax (name := rr_leadingCoeff_add_C_mul_lt_named)
  "rr_leadingCoeff_add_C_mul_lt" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

/-- Sequence form of `rr_leadingCoeff_add_C_mul_lt`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_leadingCoeff_add_C_mul_lt_sequence_named)
  "rr_leadingCoeff_add_C_mul_lt_sequence" " using "
    "parameter_ne_zero" ":=" term ","
    "degree_lt" ":=" term :
  tactic

/-- Closes the statement that, for every small `μ > 0` for which `f + C μ * g` splits, this
polynomial has a root below the fixed bound `A`. The arguments `left_pos_lc` and `right_pos_lc` are
the positivity of the leading coefficients of `f` and `g`, `succ_degree` is
`g.natDegree = f.natDegree + 1`, and `bound` is `A`. -/
syntax (name := rr_exists_root_lt_succDegree_add_right_small_named)
  "rr_exists_root_lt_succDegree_add_right_small" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "bound" ":=" term :
  tactic

/-- Sequence form of `rr_exists_root_lt_succDegree_add_right_small`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_exists_root_lt_succDegree_add_right_small_sequence_named)
  "rr_exists_root_lt_succDegree_add_right_small_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "bound" ":=" term :
  tactic

/-- Closes the local lower root-count bound for `f + C μ * g` with small `μ > 0` when
`f.natDegree < g.natDegree`: each root of `f`, with multiplicity, is matched by roots of
`f + C μ * g` within `radius` of it. The arguments are `left_splits : f.Splits`, `degree_lt`,
`radius` and `radius_pos`. -/
syntax (name := rr_degreeIncreasing_local_lower_count_named)
  "rr_degreeIncreasing_local_lower_count" " using "
    "left_splits" ":=" term ","
    "degree_lt" ":=" term ","
    "radius" ":=" term ","
    "radius_pos" ":=" term :
  tactic

/-- Sequence form of `rr_degreeIncreasing_local_lower_count`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_degreeIncreasing_local_lower_count_sequence_named)
  "rr_degreeIncreasing_local_lower_count_sequence" " using "
    "left_splits" ":=" term ","
    "degree_lt" ":=" term ","
    "radius" ":=" term ","
    "radius_pos" ":=" term :
  tactic

/-- Closes the local lower root-count bound for the pencil `f + C ν * g` for `ν` near a parameter
`μ` of an interval `[μ₀, μ₁]` on which the pencil splits and has constant degree. The arguments are
`splits_on_interval`, `degree_on_interval`, `parameter_mem : μ ∈ Set.Icc μ₀ μ₁` and `radius_pos`. -/
syntax (name := rr_positiveParameter_local_lower_count_named)
  "rr_positiveParameter_local_lower_count" " using "
    "splits_on_interval" ":=" term ","
    "degree_on_interval" ":=" term ","
    "parameter_mem" ":=" term ","
    "radius_pos" ":=" term :
  tactic

/-- Sequence form of `rr_positiveParameter_local_lower_count`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_positiveParameter_local_lower_count_sequence_named)
  "rr_positiveParameter_local_lower_count_sequence" " using "
    "splits_on_interval" ":=" term ","
    "degree_on_interval" ":=" term ","
    "parameter_mem" ":=" term ","
    "radius_pos" ":=" term :
  tactic

/-- Closes `((f + C μ * g).roots.filter (x < ·)).card = (f.roots.filter (x < ·)).card` for a pencil
of constant degree that splits and has no root at the threshold `x` on `[0, μ]`. The arguments are
`parameter_pos : 0 < μ`, `degree_on_interval`, `splits_on_interval` and `threshold_not_root`. -/
syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_named)
  "rr_rightFamily_card_roots_gt_eq_zero_param" " using "
    "parameter_pos" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

/-- Variant of `rr_rightFamily_card_roots_gt_eq_zero_param` without `using`: the certificates are
found by `rr_lookup`. -/
syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_inferred)
  "rr_rightFamily_card_roots_gt_eq_zero_param" : tactic

/-- Sequence form of `rr_rightFamily_card_roots_gt_eq_zero_param`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_sequence_named)
  "rr_rightFamily_card_roots_gt_eq_zero_param_sequence" " using "
    "parameter_pos" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

/-- Variant of `rr_rightFamily_card_roots_gt_eq_zero_param_sequence` without `using`: the
certificates are found by `rr_lookup`. -/
syntax (name := rr_rightFamily_card_roots_gt_eq_zero_param_sequence_inferred)
  "rr_rightFamily_card_roots_gt_eq_zero_param_sequence" : tactic

/-- Closes equality of the counts of roots above `x` of `f + C μ₀ * g` and `f + C μ₁ * g`, from
local lower root-count bounds on `[μ₀, μ₁]`. The arguments are `interval_order : μ₀ ≤ μ₁`,
`degree_on_interval`, `splits_on_interval`, `threshold_not_root` and `local_lower`. -/
syntax (name := rr_rightFamily_card_roots_gt_eq_local_lower_named)
  "rr_rightFamily_card_roots_gt_eq_local_lower" " using "
    "interval_order" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term ","
    "local_lower" ":=" term :
  tactic

/-- Sequence form of `rr_rightFamily_card_roots_gt_eq_local_lower`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_rightFamily_card_roots_gt_eq_local_lower_sequence_named)
  "rr_rightFamily_card_roots_gt_eq_local_lower_sequence" " using "
    "interval_order" ":=" term ","
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term ","
    "local_lower" ":=" term :
  tactic

/-- Closes `(f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card` when `f` and `g` have
positive leading coefficients and `g.natDegree = f.natDegree + 1`, by moving along the pencils
`f + C μ * g` and `g + C ν * f`. The arguments are `left_pos_lc`, `right_pos_lc`, `succ_degree`,
`left_splits`, `threshold_not_left_root`, `small_local_lower` (the local lower counts near `μ = 0`),
and the `right_family_*` and `swapped_family_*` splitting and non-root facts for the two pencils. -/
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

/-- Sequence form of `rr_card_filter_gt_endpoint_eq_local_lower`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_filter_gt_endpoint_eq_local_lower_sequence_named)
  "rr_card_filter_gt_endpoint_eq_local_lower_sequence" " using "
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

/-- Closes `(C (1 - β) * f + C β * g).eval x ≠ 0` on the closed segment `0 ≤ β ≤ 1` from
`eval_product_pos : 0 < f.eval x * g.eval x`. The arguments `parameter_nonneg` and
`parameter_le_one` bound `β`. -/
syntax (name := rr_closedSegment_eval_ne_zero_same_sign_named)
  "rr_closedSegment_eval_ne_zero_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

/-- Sequence form of `rr_closedSegment_eval_ne_zero_same_sign`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_closedSegment_eval_ne_zero_same_sign_sequence_named)
  "rr_closedSegment_eval_ne_zero_same_sign_sequence" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

/-- Closes `¬ (C (1 - β) * f + C β * g).IsRoot x` on the closed segment `0 ≤ β ≤ 1` from
`eval_product_pos : 0 < f.eval x * g.eval x`. The arguments `parameter_nonneg` and
`parameter_le_one` bound `β`. -/
syntax (name := rr_closedSegment_not_isRoot_same_sign_named)
  "rr_closedSegment_not_isRoot_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

/-- Sequence form of `rr_closedSegment_not_isRoot_same_sign`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_closedSegment_not_isRoot_same_sign_sequence_named)
  "rr_closedSegment_not_isRoot_same_sign_sequence" " using "
    "parameter_nonneg" ":=" term ","
    "parameter_le_one" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

/-- Closes `(f + C μ * g).eval x ≠ 0` from `parameter_nonneg : 0 ≤ μ` and
`eval_product_pos : 0 < f.eval x * g.eval x`. -/
syntax (name := rr_rightFamily_eval_ne_zero_same_sign_named)
  "rr_rightFamily_eval_ne_zero_same_sign" " using "
    "parameter_nonneg" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

/-- Sequence form of `rr_rightFamily_eval_ne_zero_same_sign`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rightFamily_eval_ne_zero_same_sign_sequence_named)
  "rr_rightFamily_eval_ne_zero_same_sign_sequence" " using "
    "parameter_nonneg" ":=" term ","
    "eval_product_pos" ":=" term :
  tactic

/-- Closes `∃ x', x < x' ∧ ∀ r ∈ s, r ≤ x ∨ x' < r`: a threshold can be moved up past a finite
multiset without crossing any of its elements. -/
syntax (name := rr_exists_threshold_no_mem_Ioc_named)
  "rr_exists_threshold_no_mem_Ioc" :
  tactic

/-- Sequence form of `rr_exists_threshold_no_mem_Ioc`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_exists_threshold_no_mem_Ioc_sequence_named)
  "rr_exists_threshold_no_mem_Ioc_sequence" :
  tactic

/-- Closes the existence of a threshold `x' ≥ x` that is a root of neither `f` nor `g` and leaves
both counts of roots at most the threshold unchanged. The arguments are `left_ne_zero : f ≠ 0`,
`right_ne_zero : g ≠ 0` and the starting `threshold` `x`. -/
syntax (name := rr_exists_nonRoot_threshold_count_eq_named)
  "rr_exists_nonRoot_threshold_count_eq" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "threshold" ":=" term :
  tactic

/-- Sequence form of `rr_exists_nonRoot_threshold_count_eq`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_exists_nonRoot_threshold_count_eq_sequence_named)
  "rr_exists_nonRoot_threshold_count_eq_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term :
  tactic

/-- Closes the existence of a threshold `x' ≥ x` that is a root of neither `f` nor `g` and leaves
both counts of roots above the threshold unchanged. The arguments are `left_ne_zero : f ≠ 0`,
`right_ne_zero : g ≠ 0` and the starting `threshold` `x`. -/
syntax (name := rr_exists_nonRoot_threshold_count_gt_eq_named)
  "rr_exists_nonRoot_threshold_count_gt_eq" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "threshold" ":=" term :
  tactic

/-- Sequence form of `rr_exists_nonRoot_threshold_count_gt_eq`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_exists_nonRoot_threshold_count_gt_eq_sequence_named)
  "rr_exists_nonRoot_threshold_count_gt_eq_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term :
  tactic

/-- Closes the bound `≤ 1` on both differences of the counts of roots at most `x` of `f` and `g`,
for every `x`, from `nonroot_bound`, the same bound at thresholds `x` with `f.eval x ≠ 0` and
`g.eval x ≠ 0`. The arguments `left_ne_zero` and `right_ne_zero` say that `f` and `g` are
nonzero. -/
syntax (name := rr_rootCount_diff_le_one_nonRoot_named)
  "rr_rootCount_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Sequence form of `rr_rootCount_diff_le_one_nonRoot`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rootCount_diff_le_one_nonRoot_sequence_named)
  "rr_rootCount_diff_le_one_nonRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Closes `|#{roots of f ≤ x} - #{roots of g ≤ x}| ≤ 1` for every `x` from `nonroot_bound`, the two
one-sided bounds at thresholds `x` that are roots of neither polynomial. The arguments
`left_ne_zero` and `right_ne_zero` say that `f` and `g` are nonzero. -/
syntax (name := rr_rootCount_abs_diff_le_one_nonRoot_named)
  "rr_rootCount_abs_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Sequence form of `rr_rootCount_abs_diff_le_one_nonRoot`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rootCount_abs_diff_le_one_nonRoot_sequence_named)
  "rr_rootCount_abs_diff_le_one_nonRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Variant of `rr_rootCount_diff_le_one_nonRoot` whose `nonroot_bound` is stated for thresholds `x`
with `¬ f.IsRoot x` and `¬ g.IsRoot x`. -/
syntax (name := rr_rootCount_diff_le_one_nonRoot_isRoot_named)
  "rr_rootCount_diff_le_one_nonRoot_isRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Sequence form of `rr_rootCount_diff_le_one_nonRoot_isRoot`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rootCount_diff_le_one_nonRoot_isRoot_sequence_named)
  "rr_rootCount_diff_le_one_nonRoot_isRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Closes the bound `≤ 1` on both differences of the counts of roots above `x` of `f` and `g`, for
every `x`, from `nonroot_bound`, the same bound at thresholds `x` with `f.eval x ≠ 0` and
`g.eval x ≠ 0`. The arguments `left_ne_zero` and `right_ne_zero` say that `f` and `g` are
nonzero. -/
syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_named)
  "rr_rootCountAbove_diff_le_one_nonRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Sequence form of `rr_rootCountAbove_diff_le_one_nonRoot`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_sequence_named)
  "rr_rootCountAbove_diff_le_one_nonRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Variant of `rr_rootCountAbove_diff_le_one_nonRoot` whose `nonroot_bound` is stated for
thresholds `x` with `¬ f.IsRoot x` and `¬ g.IsRoot x`. -/
syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_isRoot_named)
  "rr_rootCountAbove_diff_le_one_nonRoot_isRoot" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Sequence form of `rr_rootCountAbove_diff_le_one_nonRoot_isRoot`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_rootCountAbove_diff_le_one_nonRoot_isRoot_sequence_named)
  "rr_rootCountAbove_diff_le_one_nonRoot_isRoot_sequence" " using "
    "left_ne_zero" ":=" term ","
    "right_ne_zero" ":=" term ","
    "nonroot_bound" ":=" term :
  tactic

/-- Closes `max |lower gap| |upper gap| ≤ 1` for every threshold from `bundled_bound`, the
conjunction of the two absolute-value bounds on the counts of roots at most and above the
threshold. -/
syntax (name := rr_rootCount_max_abs_diff_le_one_named)
  "rr_rootCount_max_abs_diff_le_one" " using "
    "bundled_bound" ":=" term :
  tactic

/-- Sequence form of `rr_rootCount_max_abs_diff_le_one`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rootCount_max_abs_diff_le_one_sequence_named)
  "rr_rootCount_max_abs_diff_le_one_sequence" " using "
    "bundled_bound" ":=" term :
  tactic

/-- Closes `f.roots.card = f.natDegree` for the lower-degree member `f`. The arguments are
`left_pos_lc`, `right_pos_lc`, `pos_combo : PosComboRealRooted f g` and
`succ_degree : g.natDegree = f.natDegree + 1`. -/
syntax (name := rr_left_card_roots_succDegree_named)
  "rr_left_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Sequence form of `rr_left_card_roots_succDegree`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_left_card_roots_succDegree_sequence_named)
  "rr_left_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `g.roots.card = g.natDegree` when `succ_degree : f.natDegree = g.natDegree + 1`. The
arguments `left_pos_lc` and `right_pos_lc` give the positive leading coefficients and
`pos_combo : PosComboRealRooted f g` the real-rootedness of positive combinations. -/
syntax (name := rr_right_card_roots_succDegree_named)
  "rr_right_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Sequence form of `rr_right_card_roots_succDegree`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_right_card_roots_succDegree_sequence_named)
  "rr_right_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `f ≠ 0 ∧ f.roots.card = f.natDegree` for the lower-degree member `f`. The arguments are
`left_pos_lc`, `right_pos_lc`, `pos_combo : PosComboRealRooted f g` and
`succ_degree : g.natDegree = f.natDegree + 1`. -/
syntax (name := rr_left_ne_zero_card_roots_succDegree_named)
  "rr_left_ne_zero_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Sequence form of `rr_left_ne_zero_card_roots_succDegree`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_left_ne_zero_card_roots_succDegree_sequence_named)
  "rr_left_ne_zero_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `g ≠ 0 ∧ g.roots.card = g.natDegree` when `succ_degree : f.natDegree = g.natDegree + 1`.
The arguments `left_pos_lc` and `right_pos_lc` give the positive leading coefficients and
`pos_combo : PosComboRealRooted f g` the real-rootedness of positive combinations. -/
syntax (name := rr_right_ne_zero_card_roots_succDegree_named)
  "rr_right_ne_zero_card_roots_succDegree" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Sequence form of `rr_right_ne_zero_card_roots_succDegree`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_right_ne_zero_card_roots_succDegree_sequence_named)
  "rr_right_ne_zero_card_roots_succDegree_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "succ_degree" ":=" term :
  tactic

/-- Closes `(p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card` when `p` has no root in
`(a, b]`. The arguments are `interval_order : a ≤ b` and `no_roots`, which says that `p` has no root
`x` with `a < x ≤ b`. -/
syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_eq_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes `(p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card` when `p` has no root in
`(a, b]`. The arguments are `interval_order : a ≤ b` and `no_roots`, which says that `p` has no root
`x` with `a < x ≤ b`. -/
syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_gt_eq_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes `(p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0` when `p` has no root in `(a, b]`.
The arguments are `interval_order : a ≤ b` and `no_roots`, which says that `p` has no root `x` with
`a < x ≤ b`. -/
syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes the bundled statement that the counts of roots at most and above the threshold agree at
`a` and `b` and that `(a, b]` contains no root, when `p` has no root in `(a, b]`. The arguments are
`interval_order : a ≤ b` and `no_roots`, which says that `p` has no root `x` with `a < x ≤ b`. -/
syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_all_eq_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes `(p.roots.filter (· ≤ a)).card ≤ (p.roots.filter (· ≤ b)).card` from
`interval_order : a ≤ b`. -/
syntax (name := rr_card_roots_filter_le_mono_named)
  "rr_card_roots_filter_le_mono" " using "
    "interval_order" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_mono`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_card_roots_filter_le_mono_sequence_named)
  "rr_card_roots_filter_le_mono_sequence" " using "
    "interval_order" ":=" term :
  tactic

/-- Closes `(p.roots.filter (b < ·)).card ≤ (p.roots.filter (a < ·)).card` from
`interval_order : a ≤ b`. -/
syntax (name := rr_card_roots_filter_gt_antitone_named)
  "rr_card_roots_filter_gt_antitone" " using "
    "interval_order" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_gt_antitone`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_card_roots_filter_gt_antitone_sequence_named)
  "rr_card_roots_filter_gt_antitone_sequence" " using "
    "interval_order" ":=" term :
  tactic

/-- Closes the conjunction of `rr_card_roots_filter_le_mono` and `rr_card_roots_filter_gt_antitone`
from `interval_order : a ≤ b`. -/
syntax (name := rr_card_roots_filter_le_and_gt_mono_named)
  "rr_card_roots_filter_le_and_gt_mono" " using "
    "interval_order" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_and_gt_mono`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_card_roots_filter_le_and_gt_mono_sequence_named)
  "rr_card_roots_filter_le_and_gt_mono_sequence" " using "
    "interval_order" ":=" term :
  tactic

/-- Closes `(p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card` when `p` has no root in
`[a, b]`. The arguments are `interval_order : a ≤ b` and `no_roots`, which says that `p` has no root
`x` with `a ≤ x ≤ b`. -/
syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_eq_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes `(p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card` when `p` has no root in
`[a, b]`. The arguments are `interval_order : a ≤ b` and `no_roots`, which says that `p` has no root
`x` with `a ≤ x ≤ b`. -/
syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_gt_eq_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_gt_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_gt_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes `(p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0` when `p` has no root in `[a, b]`.
The arguments are `interval_order : a ≤ b` and `no_roots`, which says that `p` has no root `x` with
`a ≤ x ≤ b`. -/
syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_Ioc_zero_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes the bundled statement that the counts of roots at most and above the threshold agree at
`a` and `b` and that `(a, b]` contains no root, when `p` has no root in `[a, b]`. The arguments are
`interval_order : a ≤ b` and `no_roots`, which says that `p` has no root `x` with `a ≤ x ≤ b`. -/
syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_all_eq_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_all_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_all_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "no_roots" ":=" term :
  tactic

/-- Closes equality of the differences `#{roots of f ≤ t} - #{roots of g ≤ t}` at `t = a` and
`t = b` when neither `f` nor `g` has a root in `(a, b]`. The arguments are `interval_order : a ≤ b`,
and `left_no_roots` and `right_no_roots`, which say that neither `f` nor `g` has a root `x` with
`a < x ≤ b`. -/
syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Closes equality of the differences `#{roots of f > t} - #{roots of g > t}` at `t = a` and
`t = b` when neither `f` nor `g` has a root in `(a, b]`. The arguments are `interval_order : a ≤ b`,
and `left_no_roots` and `right_no_roots`, which say that neither `f` nor `g` has a root `x` with
`a < x ≤ b`. -/
syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Transports the two `≤ 1` bounds on the differences of the counts of roots at most `t` of `f` and
`g` from `t = a` to `t = b` when neither has a root in `(a, b]`. The arguments are
`interval_order : a ≤ b`, and `left_no_roots` and `right_no_roots`, which say that neither `f` nor
`g` has a root `x` with `a < x ≤ b`, and `source_bound`, the bounds at `a`. -/
syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_bound_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Transports the two `≤ 1` bounds on the differences of the counts of roots above `t` of `f` and
`g` from `t = a` to `t = b` when neither has a root in `(a, b]`. The arguments are
`interval_order : a ≤ b`, and `left_no_roots` and `right_no_roots`, which say that neither `f` nor
`g` has a root `x` with `a < x ≤ b`, and `source_bound`, the bounds at `a`. -/
syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_gt_bound_no_isRoot_Ioc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Transports both pairs of `≤ 1` bounds, for the counts of roots at most `t` and above `t`, from
`t = a` to `t = b` when neither `f` nor `g` has a root in `(a, b]`. The arguments are
`interval_order : a ≤ b`, and `left_no_roots` and `right_no_roots`, which say that neither `f` nor
`g` has a root `x` with `a < x ≤ b`, and `lower_source_bound` and `upper_source_bound`, the bounds
at `a`. -/
syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc`: the same certificate for
every index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

/-- Closes equality of the differences `#{roots of f ≤ t} - #{roots of g ≤ t}` at `t = a` and
`t = b` when neither `f` nor `g` has a root in `[a, b]`. The arguments are `interval_order : a ≤ b`,
and `left_no_roots` and `right_no_roots`, which say that neither `f` nor `g` has a root `x` with
`a ≤ x ≤ b`. -/
syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_sub_eq_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Closes equality of the differences `#{roots of f > t} - #{roots of g > t}` at `t = a` and
`t = b` when neither `f` nor `g` has a root in `[a, b]`. The arguments are `interval_order : a ≤ b`,
and `left_no_roots` and `right_no_roots`, which say that neither `f` nor `g` has a root `x` with
`a ≤ x ≤ b`. -/
syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term :
  tactic

/-- Transports the two `≤ 1` bounds on the differences of the counts of roots at most `t` of `f` and
`g` from `t = a` to `t = b` when neither has a root in `[a, b]`. The arguments are
`interval_order : a ≤ b`, and `left_no_roots` and `right_no_roots`, which say that neither `f` nor
`g` has a root `x` with `a ≤ x ≤ b`, and `source_bound`, the bounds at `a`. -/
syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_bound_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_bound_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_bound_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Transports the two `≤ 1` bounds on the differences of the counts of roots above `t` of `f` and
`g` from `t = a` to `t = b` when neither has a root in `[a, b]`. The arguments are
`interval_order : a ≤ b`, and `left_no_roots` and `right_no_roots`, which say that neither `f` nor
`g` has a root `x` with `a ≤ x ≤ b`, and `source_bound`, the bounds at `a`. -/
syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_gt_bound_no_isRoot_Icc`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_card_roots_filter_gt_bound_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_gt_bound_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "source_bound" ":=" term :
  tactic

/-- Transports both pairs of `≤ 1` bounds, for the counts of roots at most `t` and above `t`, from
`t = a` to `t = b` when neither `f` nor `g` has a root in `[a, b]`. The arguments are
`interval_order : a ≤ b`, and `left_no_roots` and `right_no_roots`, which say that neither `f` nor
`g` has a root `x` with `a ≤ x ≤ b`, and `lower_source_bound` and `upper_source_bound`, the bounds
at `a`. -/
syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

/-- Sequence form of `rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc`: the same certificate for
every index `i : Nat`. -/
syntax (name := rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence_named)
  "rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence" " using "
    "interval_order" ":=" term ","
    "left_no_roots" ":=" term ","
    "right_no_roots" ":=" term ","
    "lower_source_bound" ":=" term ","
    "upper_source_bound" ":=" term :
  tactic

end Tactic
end RealRooted
