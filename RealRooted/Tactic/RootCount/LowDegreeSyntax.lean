module

public import RealRooted.Tactic.RootCount.CoreSyntax
public import RealRooted.Tactic.RootCount.LowDegree

/-!
# Low-degree root-count tactic syntax

Parser declarations for same-degree and low-degree root-count certificates.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes
`((f + C μ₀ * g).roots.filter (x < ·)).card = ((f + C μ₁ * g).roots.filter (x < ·)).card`, the
equality of the numbers of roots above `x` at the two ends of an interval. The arguments are
`left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`pos_combo : PosComboRealRooted f g`, `same_degree : g.natDegree = f.natDegree`,
`left_parameter_nonneg : 0 ≤ μ₀`, `interval_order : μ₀ ≤ μ₁` and
`threshold_not_root : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x`. -/
syntax (name := rr_rightFamily_sameDegree_gt_count_eq_named)
  "rr_rightFamily_sameDegree_gt_count_eq" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_parameter_nonneg" ":=" term ","
    "interval_order" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

/-- Sequence form of `rr_rightFamily_sameDegree_gt_count_eq`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rightFamily_sameDegree_gt_count_eq_sequence_named)
  "rr_rightFamily_sameDegree_gt_count_eq_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_parameter_nonneg" ":=" term ","
    "interval_order" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

/-- Closes `((f + C 0 * g).roots.filter (x < ·)).card = ((f + C 1 * g).roots.filter (x < ·)).card`.
The arguments are `degree_on_interval` (the degree of `f + C μ * g` is constant for `μ ∈ [0, 1]`),
`splits_on_interval` (each `f + C μ * g` splits for `μ ∈ [0, 1]`) and `threshold_not_root` (`x` is a
root of no `f + C μ * g` with `μ ∈ [0, 1]`). -/
syntax (name := rr_rightFamily_zero_one_gt_count_eq_named)
  "rr_rightFamily_zero_one_gt_count_eq" " using "
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

/-- Sequence form of `rr_rightFamily_zero_one_gt_count_eq`: the same certificate for every index
`i : Nat`. -/
syntax (name := rr_rightFamily_zero_one_gt_count_eq_sequence_named)
  "rr_rightFamily_zero_one_gt_count_eq_sequence" " using "
    "degree_on_interval" ":=" term ","
    "splits_on_interval" ":=" term ","
    "threshold_not_root" ":=" term :
  tactic

/-- Closes `(f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card`, the equality of the
numbers of roots of `f` and `g` above `x`. The arguments are `left_pos_lc : HasPosLeadingCoeff f`,
`right_pos_lc : HasPosLeadingCoeff g`, `pos_combo : PosComboRealRooted f g`,
`same_degree : g.natDegree = f.natDegree`, `right_not_root : ¬ g.IsRoot x` and
`no_right_family_roots : ∀ μ, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x`. -/
syntax (name := rr_sameDegree_gt_count_eq_no_rightFamily_named)
  "rr_sameDegree_gt_count_eq_no_rightFamily" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

/-- Sequence form of `rr_sameDegree_gt_count_eq_no_rightFamily`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_sameDegree_gt_count_eq_no_rightFamily_sequence_named)
  "rr_sameDegree_gt_count_eq_no_rightFamily_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` strictly above `x` differ by at
most one in both directions. The arguments are `left_pos_lc : HasPosLeadingCoeff f`,
`right_pos_lc : HasPosLeadingCoeff g`, `pos_combo : PosComboRealRooted f g`,
`same_degree : g.natDegree = f.natDegree`, `right_not_root : ¬ g.IsRoot x` and
`no_right_family_roots : ∀ μ, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x`. -/
syntax (name := rr_sameDegree_rootCountAbove_no_rightFamily_named)
  "rr_sameDegree_rootCountAbove_no_rightFamily" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

/-- Sequence form of `rr_sameDegree_rootCountAbove_no_rightFamily`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_sameDegree_rootCountAbove_no_rightFamily_sequence_named)
  "rr_sameDegree_rootCountAbove_no_rightFamily_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "right_not_root" ":=" term ","
    "no_right_family_roots" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` strictly above `x` differ by at
most one in both directions. The arguments are `left_pos_lc : HasPosLeadingCoeff f`,
`right_pos_lc : HasPosLeadingCoeff g`, `pos_combo : PosComboRealRooted f g`,
`same_degree : g.natDegree = f.natDegree`, `left_not_root : ¬ f.IsRoot x`,
`right_not_root : ¬ g.IsRoot x` and
`no_positive_crossing : ¬ ∃ μ, 0 < μ ∧ (f + C μ * g).IsRoot x`. -/
syntax (name := rr_sameDegree_rootCountAbove_no_pos_crossing_named)
  "rr_sameDegree_rootCountAbove_no_pos_crossing" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "no_positive_crossing" ":=" term :
  tactic

/-- Sequence form of `rr_sameDegree_rootCountAbove_no_pos_crossing`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_sameDegree_rootCountAbove_no_pos_crossing_sequence_named)
  "rr_sameDegree_rootCountAbove_no_pos_crossing_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "no_positive_crossing" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` strictly above `x` differ by at
most one in both directions, in the case of a positive crossing. The arguments are
`left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`pos_combo : PosComboRealRooted f g`, `same_degree : g.natDegree = f.natDegree`,
`no_common_roots : ∀ r, f.IsRoot r → ¬ g.IsRoot r`, `left_not_root : ¬ f.IsRoot x`,
`right_not_root : ¬ g.IsRoot x` and `positive_crossing : ∃ μ, 0 < μ ∧ (f + C μ * g).IsRoot x`. -/
syntax (name := rr_sameDegree_rootCountAbove_pos_crossing_named)
  "rr_sameDegree_rootCountAbove_pos_crossing" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "positive_crossing" ":=" term :
  tactic

/-- Sequence form of `rr_sameDegree_rootCountAbove_pos_crossing`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_sameDegree_rootCountAbove_pos_crossing_sequence_named)
  "rr_sameDegree_rootCountAbove_pos_crossing_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "left_not_root" ":=" term ","
    "right_not_root" ":=" term ","
    "positive_crossing" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` that are at most `threshold`
differ by at most one in both directions, for `f` of degree at most two. The arguments are
`left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`pos_combo : PosComboRealRooted f g`, `same_degree : g.natDegree = f.natDegree`,
`left_degree_le_two : f.natDegree ≤ 2` and `threshold`, the real number `x`. -/
syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_two_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "threshold" ":=" term :
  tactic

/-- Sequence form of `rr_posCombo_sameDegree_rootCount_degree_le_two`: the same certificate for
every index `i : Nat`, with the threshold `x i` taken from the goal, so there is no `threshold`
argument. -/
syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_two_sequence_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_two_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` strictly above `x` differ by at
most one in both directions, for `f` of degree at most two. The arguments are
`left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`pos_combo : PosComboRealRooted f g`, `same_degree : g.natDegree = f.natDegree`,
`left_degree_le_two : f.natDegree ≤ 2` and `threshold`, the real number `x`. -/
syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_two_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "threshold" ":=" term :
  tactic

/-- Sequence form of `rr_posCombo_sameDegree_rootCountAbove_degree_le_two`: the same certificate for
every index `i : Nat`, with the threshold `x i` taken from the goal, so there is no `threshold`
argument. -/
syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

/-- Closes the same-degree root-crossing statement for `f` of degree at most one: for
`1 ≤ j < f.natDegree`, `(rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0`, and the same
with `f` and `g` swapped. The only argument is `left_degree_le_one : f.natDegree ≤ 1`. -/
syntax (name := rr_sameDegree_rootCrossing_degree_le_one_named)
  "rr_sameDegree_rootCrossing_degree_le_one" " using "
    "left_degree_le_one" ":=" term :
  tactic

/-- Sequence form of `rr_sameDegree_rootCrossing_degree_le_one`: the same certificate for every
index `i : Nat`. -/
syntax (name := rr_sameDegree_rootCrossing_degree_le_one_sequence_named)
  "rr_sameDegree_rootCrossing_degree_le_one_sequence" " using "
    "left_degree_le_one" ":=" term :
  tactic

/-- Closes the same-degree root-crossing statement for `f` of degree at most two: for
`1 ≤ j < f.natDegree`, `(rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0`, and the same
with `f` and `g` swapped. The arguments are `left_pos_lc : HasPosLeadingCoeff f`,
`right_pos_lc : HasPosLeadingCoeff g`, `pos_combo : PosComboRealRooted f g`,
`same_degree : g.natDegree = f.natDegree` and `left_degree_le_two : f.natDegree ≤ 2`. -/
syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_two_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

/-- Sequence form of `rr_posCombo_sameDegree_rootCrossing_degree_le_two`: the same certificate for
every index `i : Nat`. -/
syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` that are at most `threshold`
differ by at most one in both directions, for `f` of degree at most three. The arguments are
`left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`pos_combo : PosComboRealRooted f g`, `same_degree : g.natDegree = f.natDegree`,
`left_degree_le_three : f.natDegree ≤ 3` and `threshold`, the real number `x`. -/
syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_three_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_three" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_three" ":=" term ","
    "threshold" ":=" term :
  tactic

/-- Sequence form of `rr_posCombo_sameDegree_rootCount_degree_le_three`: the same certificate for
every index `i : Nat`, with the threshold `x i` taken from the goal, so there is no `threshold`
argument. -/
syntax (name := rr_posCombo_sameDegree_rootCount_degree_le_three_sequence_named)
  "rr_posCombo_sameDegree_rootCount_degree_le_three_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` strictly above `x` differ by at
most one in both directions, for `f` of degree at most three. The arguments are
`left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`pos_combo : PosComboRealRooted f g`, `same_degree : g.natDegree = f.natDegree`,
`left_degree_le_three : f.natDegree ≤ 3` and `threshold`, the real number `x`. -/
syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_three_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_three" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_three" ":=" term ","
    "threshold" ":=" term :
  tactic

/-- Sequence form of `rr_posCombo_sameDegree_rootCountAbove_degree_le_three`: the same certificate
for every index `i : Nat`, with the threshold `x i` taken from the goal, so there is no `threshold`
argument. -/
syntax (name := rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence_named)
  "rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

/-- Closes the same-degree root-crossing statement for `f` of degree at most three: for
`1 ≤ j < f.natDegree`, `(rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0`, and the same
with `f` and `g` swapped. The arguments are `left_pos_lc : HasPosLeadingCoeff f`,
`right_pos_lc : HasPosLeadingCoeff g`, `pos_combo : PosComboRealRooted f g`,
`same_degree : g.natDegree = f.natDegree` and `left_degree_le_three : f.natDegree ≤ 3`. -/
syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_three_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_three" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

/-- Sequence form of `rr_posCombo_sameDegree_rootCrossing_degree_le_three`: the same certificate for
every index `i : Nat`. -/
syntax (name := rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence_named)
  "rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "pos_combo" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_three" ":=" term :
  tactic

/-- Closes the statement that the numbers of roots of `f` and `g` strictly above `threshold` differ
by at most two in both directions, where `g` has degree one more than `f` and `f` has degree at most
two. The arguments are `compatible : Compatible f g`, `left_pos_lc`, `right_pos_lc`,
`succ_degree : g.natDegree = f.natDegree + 1`, `left_splits : f.Splits`,
`left_degree_le_two : f.natDegree ≤ 2` and `threshold`, the real number `x`. -/
syntax (name := rr_compatible_succDegree_rootCountAbove_le_two_named)
  "rr_compatible_succDegree_rootCountAbove_le_two" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "threshold" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_succDegree_rootCountAbove_le_two`: the same certificate for
every index `i : Nat`, with the threshold `x i` taken from the goal, so there is no `threshold`
argument. -/
syntax (name := rr_compatible_succDegree_rootCountAbove_le_two_sequence_named)
  "rr_compatible_succDegree_rootCountAbove_le_two_sequence" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term ","
    "left_degree_le_two" ":=" term :
  tactic

end Tactic
end RealRooted
