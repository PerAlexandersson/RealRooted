import RealRooted.Tactic.CommonInterleaver.Core

/-!
# Basic common-interleaver tactic syntax

Parser declarations for compatibility transports, finite-family upgrades, and
their pointwise sequence forms.
-/

namespace RealRooted
namespace Tactic

/-- Closes `Compatible g f` from `compatible : Compatible f g`. -/
syntax (name := rr_compatible_comm_named)
  "rr_compatible_comm" " using " "compatible" ":=" term :
  tactic

/-- Closes `Compatible (f.comp (X + C r)) (g.comp (X + C r))` from `compatible : Compatible f g` and
the real shift `shift : r`. -/
syntax (name := rr_compatible_comp_X_add_C_named)
  "rr_compatible_comp_X_add_C" " using "
    "compatible" ":=" term ","
    "shift" ":=" term :
  tactic

/-- Closes `Compatible (reflect N f) (reflect N g)` from `compatible : Compatible f g` and the
degree bounds `left_degree_bound : f.natDegree ≤ N` and `right_degree_bound : g.natDegree ≤ N`. -/
syntax (name := rr_compatible_reflect_named)
  "rr_compatible_reflect" " using "
    "compatible" ":=" term ","
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

/-- Closes `Compatible (reflect N f) (reflect N g) ↔ Compatible f g` from
`left_degree_bound : f.natDegree ≤ N` and `right_degree_bound : g.natDegree ≤ N`. -/
syntax (name := rr_compatible_reflect_iff_named)
  "rr_compatible_reflect_iff" " using "
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

/-- Closes `Compatible f.derivative g.derivative` from `compatible : Compatible f g`. -/
syntax (name := rr_compatible_derivative_named)
  "rr_compatible_derivative" " using " "compatible" ":=" term :
  tactic

/-- Closes `f ≠ 0 ∧ f.Splits` from `compatible : Compatible f g` and
`left_pos_lc : HasPosLeadingCoeff f`. -/
syntax (name := rr_compatible_left_realrooted_named)
  "rr_compatible_left_realrooted" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term :
  tactic

/-- Closes `g ≠ 0 ∧ g.Splits` from `compatible : Compatible f g` and
`right_pos_lc : HasPosLeadingCoeff g`. -/
syntax (name := rr_compatible_right_realrooted_named)
  "rr_compatible_right_realrooted" " using "
    "compatible" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `g.natDegree ≤ f.natDegree + 1` from `compatible : Compatible f g` and the positive
leading coefficients `left_pos_lc` of `f` and `right_pos_lc` of `g`. -/
syntax (name := rr_compatible_right_degree_le_succ_named)
  "rr_compatible_right_degree_le_succ" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `f.natDegree ≤ g.natDegree + 1 ∧ g.natDegree ≤ f.natDegree + 1` from
`compatible : Compatible f g` and the positive leading coefficients `left_pos_lc` of `f` and
`right_pos_lc` of `g`. -/
syntax (name := rr_compatible_degree_close_named)
  "rr_compatible_degree_close" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from `compatible : Compatible f g` and the positive leading
coefficients `left_pos_lc` of `f` and `right_pos_lc` of `g`. -/
syntax (name := rr_compatible_to_pos_combo_named)
  "rr_compatible_to_pos_combo" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `Compatible f g` from `pos_combo : PosComboRealRooted f g` and the real-rootedness
`left_realrooted : f ≠ 0 ∧ f.Splits` and `right_realrooted : g ≠ 0 ∧ g.Splits`. -/
syntax (name := rr_compatible_of_pos_combo_named)
  "rr_compatible_of_pos_combo" " using "
    "pos_combo" ":=" term ","
    "left_realrooted" ":=" term ","
    "right_realrooted" ":=" term :
  tactic

/-- Closes `Compatible f g` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients `left_pos_lc` and `right_pos_lc`, and `same_degree : g.natDegree = f.natDegree`. -/
syntax (name := rr_compatible_of_pos_combo_same_degree_named)
  "rr_compatible_of_pos_combo_same_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

/-- Closes `Compatible f g` from `pos_combo : PosComboRealRooted f g`, the positive leading
coefficients `left_pos_lc` and `right_pos_lc`, `succ_degree : g.natDegree = f.natDegree + 1` and
`left_splits : f.Splits`. -/
syntax (name := rr_compatible_of_pos_combo_succ_degree_named)
  "rr_compatible_of_pos_combo_succ_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_comm`: the same certificate for every index `n : Nat`. -/
syntax (name := rr_compatible_sequence_comm_named)
  "rr_compatible_sequence_comm" " using " "compatible" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_comp_X_add_C`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_comp_X_add_C_named)
  "rr_compatible_sequence_comp_X_add_C" " using "
    "compatible" ":=" term ","
    "shift" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_reflect`: the same certificate for every index `n : Nat`. -/
syntax (name := rr_compatible_sequence_reflect_named)
  "rr_compatible_sequence_reflect" " using "
    "compatible" ":=" term ","
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_reflect_iff`: the same certificate for every index `n : Nat`. -/
syntax (name := rr_compatible_sequence_reflect_iff_named)
  "rr_compatible_sequence_reflect_iff" " using "
    "left_degree_bound" ":=" term ","
    "right_degree_bound" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_derivative`: the same certificate for every index `n : Nat`. -/
syntax (name := rr_compatible_sequence_derivative_named)
  "rr_compatible_sequence_derivative" " using " "compatible" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_left_realrooted`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_left_realrooted_named)
  "rr_compatible_sequence_left_realrooted" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_right_realrooted`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_right_realrooted_named)
  "rr_compatible_sequence_right_realrooted" " using "
    "compatible" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_right_degree_le_succ`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_right_degree_le_succ_named)
  "rr_compatible_sequence_right_degree_le_succ" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_degree_close`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_degree_close_named)
  "rr_compatible_sequence_degree_close" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_to_pos_combo`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_to_pos_combo_named)
  "rr_compatible_sequence_to_pos_combo" " using "
    "compatible" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_of_pos_combo`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_of_pos_combo_named)
  "rr_compatible_sequence_of_pos_combo" " using "
    "pos_combo" ":=" term ","
    "left_realrooted" ":=" term ","
    "right_realrooted" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_of_pos_combo_same_degree`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_of_pos_combo_same_degree_named)
  "rr_compatible_sequence_of_pos_combo_same_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_of_pos_combo_succ_degree`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_of_pos_combo_succ_degree_named)
  "rr_compatible_sequence_of_pos_combo_succ_degree" " using "
    "pos_combo" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "succ_degree" ":=" term ","
    "left_splits" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from a common left interleaver `h`, given by
`common_to_left : StrictInterl h f` and `common_to_right : StrictInterl h g`, and the positive
leading coefficients `left_pos_lc` and `right_pos_lc`. -/
syntax (name := rr_compatible_of_common_left_named)
  "rr_compatible_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `PosComboRealRooted f g` from a common right interleaver `h`, given by
`left_to_common : StrictInterl f h` and `right_to_common : StrictInterl g h`, and the positive
leading coefficients `left_pos_lc` and `right_pos_lc`. -/
syntax (name := rr_compatible_of_common_right_named)
  "rr_compatible_of_common_right" " using "
    "left_to_common" ":=" term ","
    "right_to_common" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Closes `PosComboRealRooted (f.comp (X + C r)) (g.comp (X + C r))` from
`pos_combo : PosComboRealRooted f g` and the real shift `shift : r`. -/
syntax (name := rr_pos_combo_comp_X_add_C_named)
  "rr_pos_combo_comp_X_add_C" " using "
    "pos_combo" ":=" term ","
    "shift" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_of_common_left`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_of_common_left_named)
  "rr_compatible_sequence_of_common_left" " using "
    "common_to_left" ":=" term ","
    "common_to_right" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_compatible_of_common_right`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_compatible_sequence_of_common_right_named)
  "rr_compatible_sequence_of_common_right" " using "
    "left_to_common" ":=" term ","
    "right_to_common" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_pos_combo_comp_X_add_C`: the same certificate for every index `n : Nat`. -/
syntax (name := rr_pos_combo_sequence_comp_X_add_C_named)
  "rr_pos_combo_sequence_comp_X_add_C" " using "
    "pos_combo" ":=" term ","
    "shift" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs` from `common_left : HasCommonLeftInterleaver fs` and
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f`. -/
syntax (name := rr_pairwise_compatible_of_common_left_named)
  "rr_pairwise_compatible_of_common_left" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs` from `pairwise_common_left : PairwiseHasCommonLeftInterleaver fs`
and `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f`. -/
syntax (name := rr_pairwise_compatible_of_pairwise_common_left_named)
  "rr_pairwise_compatible_of_pairwise_common_left" " using "
    "pairwise_common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs` from `common_right : HasCommonInterleaver fs` and
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f`. -/
syntax (name := rr_pairwise_compatible_of_common_right_named)
  "rr_pairwise_compatible_of_common_right" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs` from `pairwise_common_right : PairwiseHasCommonInterleaver fs`
and `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f`. -/
syntax (name := rr_pairwise_compatible_of_pairwise_common_right_named)
  "rr_pairwise_compatible_of_pairwise_common_right" " using "
    "pairwise_common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Closes `HasCommonInterleaver fs` from `member_splits : ∀ f ∈ fs, f.Splits`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`pairwise_common : PairwiseHasCommonInterleaver fs`. -/
syntax (name := rr_common_interleaver_of_pairwise_named)
  "rr_common_interleaver_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common" ":=" term :
  tactic

/-- Closes `HasCommonLeftInterleaver fs` from `member_splits : ∀ f ∈ fs, f.Splits`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`pairwise_common_left : PairwiseHasCommonLeftInterleaver fs`. -/
syntax (name := rr_common_left_interleaver_of_pairwise_named)
  "rr_common_left_interleaver_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common_left" ":=" term :
  tactic

/-- Closes `fs.sum ≠ 0 ∧ fs.sum.Splits` from `common_right : HasCommonInterleaver fs`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and `nonempty : fs ≠ []`. -/
syntax (name := rr_common_interleaver_sum_realrooted_named)
  "rr_common_interleaver_sum_realrooted" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

/-- Closes `fs.sum ≠ 0 ∧ fs.sum.Splits` from `common_left : HasCommonLeftInterleaver fs`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and `nonempty : fs ≠ []`. -/
syntax (name := rr_common_left_interleaver_sum_realrooted_named)
  "rr_common_left_interleaver_sum_realrooted" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

/-- Sequence form of `rr_pairwise_compatible_of_common_left`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_pairwise_compatible_sequence_of_common_left_named)
  "rr_pairwise_compatible_sequence_of_common_left" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_pairwise_compatible_of_pairwise_common_left`: the same certificate for
every index `n : Nat`. -/
syntax (name := rr_pairwise_compatible_sequence_of_pairwise_common_left_named)
  "rr_pairwise_compatible_sequence_of_pairwise_common_left" " using "
    "pairwise_common_left" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_pairwise_compatible_of_common_right`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_pairwise_compatible_sequence_of_common_right_named)
  "rr_pairwise_compatible_sequence_of_common_right" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_pairwise_compatible_of_pairwise_common_right`: the same certificate for
every index `n : Nat`. -/
syntax (name := rr_pairwise_compatible_sequence_of_pairwise_common_right_named)
  "rr_pairwise_compatible_sequence_of_pairwise_common_right" " using "
    "pairwise_common_right" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

/-- Sequence form of `rr_common_interleaver_of_pairwise`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_common_interleaver_sequence_of_pairwise_named)
  "rr_common_interleaver_sequence_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common" ":=" term :
  tactic

/-- Sequence form of `rr_common_left_interleaver_of_pairwise`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_common_left_interleaver_sequence_of_pairwise_named)
  "rr_common_left_interleaver_sequence_of_pairwise" " using "
    "member_splits" ":=" term ","
    "member_pos_lc" ":=" term ","
    "pairwise_common_left" ":=" term :
  tactic

/-- Sequence form of `rr_common_interleaver_sum_realrooted`: the same certificate for every index
`n : Nat`. -/
syntax (name := rr_common_interleaver_sum_sequence_realrooted_named)
  "rr_common_interleaver_sum_sequence_realrooted" " using "
    "common_right" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

/-- Sequence form of `rr_common_left_interleaver_sum_realrooted`: the same certificate for every
index `n : Nat`. -/
syntax (name := rr_common_left_interleaver_sum_sequence_realrooted_named)
  "rr_common_left_interleaver_sum_sequence_realrooted" " using "
    "common_left" ":=" term ","
    "member_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

end Tactic
end RealRooted
