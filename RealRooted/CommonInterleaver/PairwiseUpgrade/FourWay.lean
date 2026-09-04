/-
# Four-way finite-family common-interleaver packages

This module assembles pairwise compatibility, pairwise and global common
interleavers, and full family compatibility into reusable finite-family
four-way package witnesses. Equivalence projections and endpoint-specific
corollaries live in `PairwiseUpgrade.FourWay.Equivalences`.
-/
import RealRooted.CommonInterleaver.PairwiseUpgrade

open Polynomial

noncomputable section

namespace RealRooted

/-- The finite-family four-way Chudnovsky--Seymour package used by this
project: pairwise compatibility, pairwise common right interleavers, global
common right interleaver, and full nonnegative family compatibility. -/
abbrev ChudnovskySeymourFourWayPackage (fs : List ℝ[X]) : Prop :=
  (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
    (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
    (HasCommonInterleaver fs ↔ FamilyCompatible fs)

private theorem chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (h12 : PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) :
    ChudnovskySeymourFourWayPackage fs := by
  have h23 : PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
    ⟨commonInterleaverFamilyUpgrade
        (fun f hf => (hrr f hf).2) hpos,
      pairwiseHasCommonInterleaver_of_commonInterleaver⟩
  have h34 : HasCommonInterleaver fs ↔ FamilyCompatible fs :=
    ⟨fun hcommon => familyCompatible_of_commonInterleaver hcommon hpos,
      fun hfull => h23.1 (h12.1 (pairwiseCompatible_of_familyCompatible hfull))⟩
  exact ⟨h12, h23, h34⟩

/-- Internal four-way assembly bridge shared with the low-degree package. -/
protected theorem PairwiseUpgrade.fourWay_of_pairwiseCommonForward
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hforward : PairwiseCompatible fs → PairwiseHasCommonInterleaver fs) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon hrr hpos
    ⟨hforward, fun hpair => pairwiseCompatible_of_pairwiseHasCommonInterleaver hpair hpos⟩

/-- Chudnovsky--Seymour four-way package in the finite-list language used in
this project, with the two-polynomial converse isolated as hypothesis:

1. pairwise compatibility,
2. pairwise common right interleavers,
3. a global common right interleaver,
4. full nonnegative family compatibility. -/
theorem chudnovskySeymour_fourWay_of_pairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonRightInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  PairwiseUpgrade.fourWay_of_pairwiseCommonForward hrr hpos <|
    pairwiseHasCommonInterleaver_of_pairwiseCompatible htwo hpos

/-- Chudnovsky--Seymour four-way package with the natural two-polynomial bridge
assumption (requiring positive leading coefficients on the pair). -/
theorem chudnovskySeymour_fourWay_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  PairwiseUpgrade.fourWay_of_pairwiseCommonForward hrr hpos <|
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos htwo hpos

/-- Four-way Chudnovsky--Seymour package from the honest same-degree/succ-degree
compatibility split. -/
theorem chudnovskySeymour_fourWay_of_compatibleDegreeSplit
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_degreeSplit hsame hsucc)

/-- Four-way Chudnovsky--Seymour package from the repaired shifted
nonnegative-coefficient degree split. -/
theorem chudnovskySeymour_fourWay_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      hsame hsucc)

/-- Four-way Chudnovsky--Seymour package from the concrete slot-data endpoints
for the nonnegative same-degree and succ-degree branches, upgraded by the
nonnegative-shift reduction. -/
theorem chudnovskySeymour_fourWay_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_slotData_via_nonnegShift hsame hsucc)

/-- Four-way Chudnovsky--Seymour package from the root-crossing formulations
of the same-degree and succ-degree branches, upgraded by the nonnegative-shift
reduction. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
      hsame hsplit hsucc)

/-- Four-way Chudnovsky--Seymour package from root-crossing formulations alone.
The succ-degree left endpoint is supplied by root continuity before shifting. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing_via_nonnegShift
    hrr hpos hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc

/-- Four-way Chudnovsky--Seymour package from root-crossing formulations, with
the succ-degree left endpoint supplied by the PF/ASW route before shifting. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_rootCrossing_and_forward_asw
      hsame hASW hsucc)

/-- Four-way Chudnovsky--Seymour package from root-crossing formulations, with
the succ-degree left endpoint supplied by the splitting-only ASW target before
shifting. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw
    (fs := fs) hrr hpos hsame
    (aissenSchoenbergWhitneyForwardOrZero_of_splits hASW) hsucc

/-- Four-way Chudnovsky--Seymour package from the nonnegative-coefficient
degree-split package, upgraded to arbitrary positive-leading families by a
common translation trick applied pairwise. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_via_nonnegShift
    (fs := fs) hrr hpos
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg
      hsame)
    hsucc

/-- Four-way Chudnovsky--Seymour package after the nonnegative shift
reduction, with the succ-degree branch discharged by the affine-family bridge.
-/
theorem chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_degreeSplit_via_nonnegShift
    (fs := fs) hrr hpos hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Four-way Chudnovsky--Seymour package from the stronger boundary-right-pair
statement, upgraded to arbitrary positive-leading families by the shift
reduction. -/
theorem chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_via_nonnegShift
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_sameDegreeAlternative_and_affineFamily_via_nonnegShift
    (fs := fs) hrr hpos
    (boundaryRightPairOrientation_implies_sameDegreeOrientationAlternative_nonneg
      hboundary)
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

/-- Same four-way Chudnovsky--Seymour package, with assumptions phrased via the
positive-combination two-polynomial bridge. -/
theorem chudnovskySeymour_fourWay_of_posComboBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hposComboBridge : PosComboPairHasCommonInterleaverStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos
    (hrr := hrr) (hpos := hpos)
    (compatiblePairHasCommonInterleaver_of_posComboPair hposComboBridge)

/-- Same four-way package from the reduced positive-combo ingredients:
no-common orientation and degree closeness for `PosComboRealRooted` pairs. -/
theorem chudnovskySeymour_fourWay_of_noCommonOrientation_and_degreeClose
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hstep : PosComboNoCommonOrientationStatement)
    (hdegClose : PosComboNatDegreeCloseStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_posComboBridge
    (hrr := hrr) (hpos := hpos)
    (posComboPairHasCommonInterleaver_of_noCommonOrientation_and_degreeClose
      hstep hdegClose)

/-- Internal four-way package constructor shared with the equivalence layer. -/
protected theorem PairwiseUpgrade.fourWay_of_nonnegPairBridge
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
    ChudnovskySeymourFourWayPackage fs :=
  PairwiseUpgrade.fourWay_of_pairwiseCommonForward hrr hpos <|
    PairwiseUpgrade.pairwiseHasCommonInterleaver_of_nonnegPairBridge hbridge hpos hnn

/-- Four-way Chudnovsky--Seymour package from no-common orientation in the
nonnegative-coefficient regime (where degree closeness is automatic). -/
theorem chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hstep : PosComboNoCommonOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  PairwiseUpgrade.fourWay_of_nonnegPairBridge hrr hpos hnn
    (PairwiseUpgrade.nonnegPairBridge_of_noCommonOrientation hstep)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the repaired degree split: both same-degree and succ-degree no-common
branches are stated directly as common-interleaver bridges. -/
theorem chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  PairwiseUpgrade.fourWay_of_nonnegPairBridge hrr hpos hnn
    (PairwiseUpgrade.nonnegPairBridge_of_pairDegreeSplit hsame hsucc)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the honest same-degree/succ-degree split, where the succ-degree branch is
stated directly as a common-interleaver bridge. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg hsame)
    hsucc

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime,
using the repaired same-degree branch and the affine-family bridge for the
succ-degree branch. -/
theorem chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn hsame
    (posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haffBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the all-combinations bridge. -/
theorem chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonOrientation_of_allComboBridge hallBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the affine-family bridge. -/
theorem chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  PairwiseUpgrade.fourWay_of_nonnegPairBridge hrr hpos hnn
    (PairwiseUpgrade.nonnegPairBridge_of_affineFamilyBridge haffBridge)

/-- Four-way Chudnovsky--Seymour package in the nonnegative-coefficient regime
from the boundary-right-pair orientation statement. -/
theorem chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_and_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
    (fs := fs) hrr hpos hnn
    (posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary)

end RealRooted
