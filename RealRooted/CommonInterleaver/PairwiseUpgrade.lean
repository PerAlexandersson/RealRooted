/-
# Pairwise finite-family common-interleaver upgrades

This module lifts compatible pairs and pair-bridge hypotheses to pairwise
common-interleaver witnesses. Generic global and full-family compatibility
packaging lives in `PairwiseUpgrade.FamilyCompatibility`.
-/
import RealRooted.CommonInterleaver.PairBridge

open Polynomial

noncomputable section

namespace RealRooted

/-- Internal nonnegative pair bridge shared with the four-way package. -/
protected theorem PairwiseUpgrade.nonnegPairBridge_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      Compatible f g →
      ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    compatiblePairHasCommonInterleaver_of_noCommonOrientation_and_nonnegCoeffs
      hstep hf_pos hg_pos hfnn hgnn hfg

/-- Internal degree-split pair bridge shared with the four-way package. -/
protected theorem PairwiseUpgrade.nonnegPairBridge_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      Compatible f g →
      ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    compatiblePairHasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
      hsame hsucc hf_pos hg_pos hfnn hgnn hfg

/-- Internal affine-family pair bridge shared with the four-way package. -/
protected theorem PairwiseUpgrade.nonnegPairBridge_of_affineFamilyBridge
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    ∀ ⦃f g : ℝ[X]⦄,
      HasPosLeadingCoeff f →
      HasPosLeadingCoeff g →
      HasNonnegCoeffs f →
      HasNonnegCoeffs g →
      Compatible f g →
      ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  fun {_ _} hf_pos hg_pos hfnn hgnn hfg =>
    compatiblePairHasCommonInterleaver_of_affineFamilyBridge_and_nonnegCoeffs
      haffBridge hf_pos hg_pos hfnn hgnn hfg

/-- Pairwise upgrade using the natural positive-leading two-polynomial bridge. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    {fs : List ℝ[X]}
    (htwo : CompatiblePairHasCommonInterleaverStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    htwo
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hpair i j hij)

/-- Pairwise upgrade from the repaired shifted nonnegative-coefficient
degree-split package. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairDegreeSplit_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from the slot-data endpoints after shifting each pair
into the nonnegative regime. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_slotData_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_slotData_via_nonnegShift hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from the root-crossing formulations after shifting each
pair into the nonnegative regime. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing_via_nonnegShift
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCrossing_via_nonnegShift
      hsame hsplit hsucc)
    hpos hpair

/-- Pairwise upgrade from root-crossing formulations alone.  The succ-degree
left endpoint is supplied by root continuity before shifting. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing_via_nonnegShift
    hsame PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity hsucc hpos hpair

/-- Pairwise upgrade from lower-threshold root-count formulations. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCrossing
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc) hpos hpair

/-- Pairwise upgrade from upper-threshold root-count formulations in both the
same-degree and succ-degree branches. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCountAboveBoth hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from common-non-root lower-threshold root-count
formulations in both branches. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountNonRoot
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCountNonRoot hsame hsucc)
    hpos hpair

/-- Pairwise upgrade from common-non-root upper-threshold root-count
formulations in both branches. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBothNonRoot
    {fs : List ℝ[X]}
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    (compatiblePairHasCommonInterleaver_of_rootCountAboveBothNonRoot hsame hsucc)
    hpos hpair

/-- Internal pairwise-family lift shared with the four-way package. -/
protected theorem PairwiseUpgrade.pairwiseHasCommonInterleaver_of_nonnegPairBridge
    {fs : List ℝ[X]}
    (hbridge :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        Compatible f g →
        ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    hbridge
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hnn (fs.get i) (List.get_mem _ _))
      (hnn (fs.get j) (List.get_mem _ _))
      (hpair i j hij)

end RealRooted
