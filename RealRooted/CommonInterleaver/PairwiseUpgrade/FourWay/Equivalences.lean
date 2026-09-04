/-
# Four-way finite-family equivalences

This module extracts equivalences from four-way common-interleaver packages
and provides their endpoint-specific compatibility corollaries.
-/
import RealRooted.CommonInterleaver.PairwiseUpgrade.FourWay

open Polynomial

noncomputable section

namespace RealRooted

/-- Extract the `1 ↔ 2` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  hfour.1

/-- Extract the `2 ↔ 3` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  hfour.2.1

/-- Extract the `3 ↔ 4` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem hasCommonInterleaver_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  hfour.2.2

/-- Extract the `1 ↔ 3` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  (pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay hfour).trans
    (pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay hfour)

/-- Extract the `1 ↔ 4` Chudnovsky--Seymour equivalence from the four-way
package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : ChudnovskySeymourFourWayPackage fs) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  (pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay hfour).trans
    (hasCommonInterleaver_iff_familyCompatible_of_fourWay hfour)

/-- Chudnovsky--Seymour `1 ↔ 3` corollary under the natural positive-leading
pair bridge. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_pairBridgePos
      (fs := fs) hrr hpos htwo

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the honest same-degree /
succ-degree compatibility split. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_compatibleDegreeSplit
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the repaired shifted
nonnegative-coefficient degree split. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_pairDegreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the concrete slot-data
endpoints after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_slotData_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the root-crossing
formulations after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_rootCrossing_via_nonnegShift
      (fs := fs) hrr hpos hsame hsplit hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from root-crossing formulations
alone.  Root continuity supplies the succ-degree left endpoint. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
    hrr hpos hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from root-crossing formulations, with
the succ-degree left endpoint supplied by the PF/ASW route before shifting. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw
      (fs := fs) hrr hpos hsame hASW hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from root-crossing formulations, with
the succ-degree left endpoint supplied by the splitting-only ASW target before
shifting. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
    (fs := fs) hrr hpos hsame
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the nonnegative-coefficient
degree-split package, with the familywise nonnegativity assumption removed by
translation. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc

/-- Chudnovsky--Seymour `1 ↔ 3` corollary after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem
    pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
      (fs := fs) hrr hpos hsame haffBridge

/-- Chudnovsky--Seymour `1 ↔ 3` corollary from the stronger
boundary-right-pair statement after the nonnegative shift reduction. -/
theorem
    pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
      (fs := fs) hrr hpos hboundary

/-- Chudnovsky--Seymour `1 ↔ 4` corollary under the natural positive-leading
pair bridge: pairwise compatibility is equivalent to full family
compatibility. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos
      (fs := fs) hrr hpos htwo).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the honest same-degree /
succ-degree compatibility split. -/
theorem pairwiseCompatible_iff_familyCompatible_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_compatibleDegreeSplit
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the repaired shifted
nonnegative-coefficient degree split. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the concrete slot-data
endpoints after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_familyCompatible_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the root-crossing
formulations after the nonnegative-shift reduction. -/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
      (fs := fs) hrr hpos hsame hsplit hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from root-crossing formulations
alone.  Root continuity supplies the succ-degree left endpoint. -/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_rootCrossing_via_nonnegShift
    hrr hpos hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from root-crossing formulations,
with the succ-degree left endpoint supplied by the PF/ASW route before shifting.
-/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
      (fs := fs) hrr hpos hsame hASW hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from root-crossing formulations,
with the succ-degree left endpoint supplied by the splitting-only ASW target
before shifting. -/
theorem pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw
    (fs := fs) hrr hpos hsame
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the nonnegative-coefficient
degree-split package, with the familywise nonnegativity assumption removed by
translation. -/
theorem pairwiseCompatible_iff_familyCompatible_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_via_nonnegShift
      (fs := fs) hrr hpos hsame hsucc).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem
    pairwiseCompatible_iff_familyCompatible_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
      (fs := fs) hrr hpos hsame haffBridge).1

/-- Chudnovsky--Seymour `1 ↔ 4` specialization from the stronger
boundary-right-pair statement after the nonnegative shift reduction. -/
theorem pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_via_nonnegShift
      (fs := fs) hrr hpos hboundary).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from a direct nonnegative pair bridge. -/
private theorem pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        Compatible f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay <|
    PairwiseUpgrade.fourWay_of_nonnegPairBridge hrr hpos hnn hbridge

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the no-common orientation core. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge hrr hpos hnn
    (PairwiseUpgrade.nonnegPairBridge_of_noCommonOrientation hstep)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the repaired degree-split package. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge hrr hpos hnn
    (PairwiseUpgrade.nonnegPairBridge_of_pairDegreeSplit hsame hsucc)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the honest degree-split package. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the all-combinations bridge. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the affine-family bridge. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_nonnegPairBridge hrr hpos hnn
    (PairwiseUpgrade.nonnegPairBridge_of_affineFamilyBridge haffBridge)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 3`
from the boundary-right-pair orientation statement. -/
theorem pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the no-common orientation core. -/
theorem pairwiseCompatible_iff_familyCompatible_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hstep).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the repaired degree-split package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hsame hsucc).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the honest degree-split package. -/
theorem pairwiseCompatible_iff_familyCompatible_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hsame hsucc).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem pairwiseCompatible_iff_familyCompatible_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_sameDegreePair_and_affineFamily_nonneg
      (fs := fs) hrr hpos hnn hsame haffBridge).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the all-combinations bridge. -/
theorem pairwiseCompatible_iff_familyCompatible_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_allComboBridge_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hallBridge).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the affine-family bridge. -/
theorem pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn haffBridge).1

/-- Nonnegative-coefficient specialization of Chudnovsky--Seymour `1 ↔ 4`
from the boundary-right-pair orientation statement. -/
theorem pairwiseCompatible_iff_familyCompatible_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos <|
    (pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
      (fs := fs) hrr hpos hnn hboundary).1

end RealRooted
