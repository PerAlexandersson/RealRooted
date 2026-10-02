import RealRooted.CommonInterleaver.PairBridge.Forward

/-!
# Succ-degree root counts from a common left interleaver
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Common-left-interleaver formulation of the succ-degree no-common
root-count bound, kept only for its `LiuOppositeSigns` callers. -/
def PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    ∃ h : ℝ[X], StrictInterl h f ∧ StrictInterl h g

/-- A common left interleaver gives the succ-degree common-non-root upper
root-count bound.  The degrees force the left interleaver to have the same
degree as `f`, so the same-degree and tight succ-degree oriented count bounds
combine directly. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver
    (hleft : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x _hxf _hxg
  obtain ⟨h, hhf, hhg⟩ :=
    hleft hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  refine (succDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
    hf_split hg_split hdeg x).mpr ?_
  have hhf_le := hhf.natDegree_le
  have hhg_le_succ := hhg.natDegree_le_succ
  have hdh : f.natDegree = h.natDegree := by lia
  have hdg : g.natDegree = h.natDegree + 1 := by lia
  obtain ⟨hA1, hA2⟩ := sameDegreeRootCountOriented_of_strictInterl hhf hdh x
  obtain ⟨hB1, hB2⟩ := succDegreeRootCountLowerOriented_of_strictInterl hhg hdg x
  exact ⟨by lia, by lia⟩

end RealRooted
