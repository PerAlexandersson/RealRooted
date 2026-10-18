import RealRooted.Tactic.CommonInterleaver.FamilySyntax

/-!
# Low-degree common-interleaver tactic syntax

Parser declarations for degree-at-most-three pair and family endpoints.
-/

namespace RealRooted
namespace Tactic

/-- Closes `∃ h, StrictInterl f h ∧ StrictInterl g h` for two polynomials of degree at most two. The
arguments are `left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`left_splits : f.Splits`, `right_splits : g.Splits`, `pos_combo : PosComboRealRooted f g`,
`left_degree_le_two : f.natDegree ≤ 2` and `right_degree_le_two : g.natDegree ≤ 2`. -/
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

/-- Closes `∃ h, StrictInterl f h ∧ StrictInterl g h` for two polynomials of degree at most two. The
arguments are `left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`compatible : Compatible f g`, `left_degree_le_two : f.natDegree ≤ 2` and
`right_degree_le_two : g.natDegree ≤ 2`. -/
syntax (name := rr_compatible_pair_common_interleaver_degree_le_two_named)
  "rr_compatible_pair_common_interleaver_degree_le_two" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term ","
    "left_degree_le_two" ":=" term ","
    "right_degree_le_two" ":=" term :
  tactic

/-- Closes `∃ h, StrictInterl f h ∧ StrictInterl g h` for two polynomials of degree at most one,
from `left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`left_degree_le_one : f.natDegree ≤ 1` and `right_degree_le_one : g.natDegree ≤ 1`. -/
syntax (name := rr_pair_common_interleaver_degree_le_one_named)
  "rr_pair_common_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
  tactic

/-- Closes `∃ h, StrictInterl h f ∧ StrictInterl h g` (a common left interleaver) for two
polynomials of degree at most one, from `left_pos_lc : HasPosLeadingCoeff f`,
`right_pos_lc : HasPosLeadingCoeff g`, `left_degree_le_one : f.natDegree ≤ 1` and
`right_degree_le_one : g.natDegree ≤ 1`. -/
syntax (name := rr_pair_common_left_interleaver_degree_le_one_named)
  "rr_pair_common_left_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
  tactic

/-- Closes `∃ h, StrictInterl f h ∧ StrictInterl g h` for two polynomials of the same degree at most
one, from `left_pos_lc : HasPosLeadingCoeff f`, `right_pos_lc : HasPosLeadingCoeff g`,
`same_degree : g.natDegree = f.natDegree` and `left_degree_le_one : f.natDegree ≤ 1`. -/
syntax (name := rr_pair_common_interleaver_sameDegree_degree_le_one_named)
  "rr_pair_common_interleaver_sameDegree_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_one" ":=" term :
  tactic

/-- Closes `∃ h, StrictInterl h f ∧ StrictInterl h g` (a common left interleaver) for two
polynomials of the same degree at most one, from `left_pos_lc : HasPosLeadingCoeff f`,
`right_pos_lc : HasPosLeadingCoeff g`, `same_degree : g.natDegree = f.natDegree` and
`left_degree_le_one : f.natDegree ≤ 1`. -/
syntax (name := rr_pair_common_left_interleaver_sameDegree_degree_le_one_named)
  "rr_pair_common_left_interleaver_sameDegree_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "same_degree" ":=" term ","
    "left_degree_le_one" ":=" term :
  tactic

/-- Closes `∃ h, StrictInterl f h ∧ StrictInterl g h` for two polynomials of degree at most one. The
arguments are `left_pos_lc`, `right_pos_lc`, `compatible : Compatible f g`, `left_degree_le_one` and
`right_degree_le_one`; the proof does not use `compatible`, since degree at most one already
suffices. -/
syntax (name := rr_compatible_pair_common_interleaver_degree_le_one_named)
  "rr_compatible_pair_common_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
  tactic

/-- Closes `∃ h, StrictInterl h f ∧ StrictInterl h g` (a common left interleaver) for two
polynomials of degree at most one. The arguments are `left_pos_lc`, `right_pos_lc`,
`compatible : Compatible f g`, `left_degree_le_one` and `right_degree_le_one`; the proof does not
use `compatible`. -/
syntax (name := rr_compatible_pair_common_left_interleaver_degree_le_one_named)
  "rr_compatible_pair_common_left_interleaver_degree_le_one" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term ","
    "left_degree_le_one" ":=" term ","
    "right_degree_le_one" ":=" term :
  tactic

/-- Closes `PairwiseHasCommonInterleaver fs` for a list `fs` of polynomials of degree at most one,
from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_one : ∀ f ∈ fs, f.natDegree ≤ 1`. -/
syntax (name := rr_pairwise_common_interleaver_degree_le_one_named)
  "rr_pairwise_common_interleaver_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

/-- Closes `PairwiseHasCommonInterleaver fs` for a list `fs` of polynomials of degree at most two,
from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f`,
`member_degree_le_two : ∀ f ∈ fs, f.natDegree ≤ 2` and
`pairwise_compatible : PairwiseCompatible fs`. -/
syntax (name := rr_pairwise_common_interleaver_degree_le_two_named)
  "rr_pairwise_common_interleaver_degree_le_two" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term ","
    "pairwise_compatible" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs` for a list `fs` of polynomials
of degree at most one, from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_one : ∀ f ∈ fs, f.natDegree ≤ 1`. -/
syntax (name := rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_one_named)
  "rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs` for a list `fs` of polynomials
of degree at most two, from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_two : ∀ f ∈ fs, f.natDegree ≤ 2`. -/
syntax (name := rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_two_named)
  "rr_pairwiseCompatible_iff_pairwiseCommon_degree_le_two" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

/-- Closes `PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs` for a list `fs` of
polynomials of degree at most one, from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_one : ∀ f ∈ fs, f.natDegree ≤ 1`. -/
syntax (name := rr_pairwiseCommon_iff_commonInterleaver_degree_le_one_named)
  "rr_pairwiseCommon_iff_commonInterleaver_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

/-- Closes `PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs` for a list `fs` of
polynomials of degree at most two, from `member_realrooted : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_two : ∀ f ∈ fs, f.natDegree ≤ 2`. -/
syntax (name := rr_pairwiseCommon_iff_commonInterleaver_degree_le_two_named)
  "rr_pairwiseCommon_iff_commonInterleaver_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

/-- Closes `HasCommonInterleaver fs ↔ FamilyCompatible fs` for a list `fs` of polynomials of degree
at most one, from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_one : ∀ f ∈ fs, f.natDegree ≤ 1`. -/
syntax (name := rr_commonInterleaver_iff_familyCompatible_degree_le_one_named)
  "rr_commonInterleaver_iff_familyCompatible_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

/-- Closes `HasCommonInterleaver fs ↔ FamilyCompatible fs` for a list `fs` of polynomials of degree
at most two, from `member_realrooted : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_two : ∀ f ∈ fs, f.natDegree ≤ 2`. -/
syntax (name := rr_commonInterleaver_iff_familyCompatible_degree_le_two_named)
  "rr_commonInterleaver_iff_familyCompatible_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs ↔ HasCommonInterleaver fs` for a list `fs` of polynomials of
degree at most one, from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_one : ∀ f ∈ fs, f.natDegree ≤ 1`. -/
syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_degree_le_one_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs ↔ HasCommonInterleaver fs` for a list `fs` of polynomials of
degree at most two, from `member_realrooted : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_two : ∀ f ∈ fs, f.natDegree ≤ 2`. -/
syntax (name := rr_pairwiseCompatible_iff_commonInterleaver_degree_le_two_named)
  "rr_pairwiseCompatible_iff_commonInterleaver_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs` for a list `fs` of polynomials of
degree at most one, from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_one : ∀ f ∈ fs, f.natDegree ≤ 1`. -/
syntax (name := rr_pairwiseCompatible_iff_commonLeft_degree_le_one_named)
  "rr_pairwiseCompatible_iff_commonLeft_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs ↔ FamilyCompatible fs` for a list `fs` of polynomials of degree at
most one, from `member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_one : ∀ f ∈ fs, f.natDegree ≤ 1`. -/
syntax (name := rr_pairwiseCompatible_iff_familyCompatible_degree_le_one_named)
  "rr_pairwiseCompatible_iff_familyCompatible_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

/-- Closes `PairwiseCompatible fs ↔ FamilyCompatible fs` for a list `fs` of polynomials of degree at
most two, from `member_realrooted : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits`,
`member_pos_lc : ∀ f ∈ fs, HasPosLeadingCoeff f` and
`member_degree_le_two : ∀ f ∈ fs, f.natDegree ≤ 2`. -/
syntax (name := rr_pairwiseCompatible_iff_familyCompatible_degree_le_two_named)
  "rr_pairwiseCompatible_iff_familyCompatible_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

end Tactic
end RealRooted
