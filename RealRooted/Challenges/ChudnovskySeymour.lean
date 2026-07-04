import RealRooted.ChudnovskySeymour
import RealRooted.CommonInterleaverSeq

/-!
# Chudnovsky--Seymour challenge entry point

This module exposes the roadmap target statements and a small solved
low-degree package for the Chudnovsky--Seymour compatibility/common-interleaver
machinery.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace ChudnovskySeymour

/-- Four-way compatibility/common-interleaver package for a finite family. -/
abbrev fourWayPackage (fs : List ℝ[X]) : Prop :=
  ChudnovskySeymourFourWayPackage fs

/-- Challenge-facing projection from the four-way package to `1 ↔ 2`. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `2 ↔ 3`. -/
theorem pairwiseHasCommonInterleaver_iff_commonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `3 ↔ 4`. -/
theorem commonInterleaver_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  RealRooted.hasCommonInterleaver_iff_familyCompatible_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `1 ↔ 3`. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `1 ↔ 4`. -/
theorem pairwiseCompatible_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  (pairwiseCompatible_iff_commonInterleaver_of_fourWay hfour).trans
    (commonInterleaver_iff_familyCompatible_of_fourWay hfour)

/-- Roadmap target for pairwise compatibility versus common left interleavers. -/
abbrev commonLeftInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target

/-- Roadmap target for pairwise compatibility versus common right interleavers. -/
abbrev commonInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target

/-- Roadmap target for the nonnegative-coefficient common right interleaver
form. -/
abbrev commonInterleaverNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target

/-- Roadmap target for the nonnegative-coefficient finite-family compatibility
form. -/
abbrev familyCompatibleNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target

/-- Roadmap target for the nonnegative-coefficient four-way package. -/
abbrev fourWayNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_fourWay_nonnegCoeffs_target

/-! ## Pair endpoint targets for milestones B1 and B2 -/

/-- Milestone B1 (#41): repaired same-degree no-common pair endpoint. -/
abbrev sameDegreePairTarget : Prop :=
  PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement

/-- Strong same-degree orientation alternative used by several reductions. -/
abbrev sameDegreeOrientationAlternativeTarget : Prop :=
  PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement

/-- Same-degree root-slot reformulation of milestone B1. -/
abbrev sameDegreeSlotDataTarget : Prop :=
  PosComboNoCommonSameDegreeSlotDataNonnegStatement

/-- Same-degree descending-root crossing subtarget for milestone B1. -/
abbrev sameDegreeRootCrossingTarget : Prop :=
  PosComboNoCommonSameDegreeRootCrossingNonnegStatement

/-- Milestone B2 (#42): repaired succ-degree no-common pair endpoint. -/
abbrev succDegreePairTarget : Prop :=
  PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement

/-- Strong fixed-orientation succ-degree endpoint. -/
abbrev succDegreeOrientationTarget : Prop :=
  PosComboNoCommonSuccDegreeOrientationNonnegStatement

/-- Succ-degree left-endpoint real-rootedness subtarget. -/
abbrev succDegreeLeftSplitsTarget : Prop :=
  PosComboSuccDegreeLeftSplitsNonnegStatement

/-- Residual succ-degree left-endpoint target after removing the nonzero
constant-term and common-`X` branches. -/
abbrev succDegreeResidualLeftSplitsTarget : Prop :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement

/-- Zero-aware forward Aissen--Schoenberg--Whitney target used by the PF-limit
left-endpoint route. -/
abbrev forwardASWTarget : Prop :=
  aissenSchoenbergWhitneyForwardOrZeroStatement

/-- Splitting-only forward Aissen--Schoenberg--Whitney target; this is now
equivalent to the zero-aware target used by the PF-limit route. -/
abbrev forwardASWSplitsTarget : Prop :=
  aissenSchoenbergWhitneyForwardSplitsStatement

/-- Succ-degree root-slot reformulation of milestone B2. -/
abbrev succDegreeSlotDataTarget : Prop :=
  PosComboNoCommonSuccDegreeSlotDataNonnegStatement

/-- Succ-degree descending-root crossing subtarget for milestone B2. -/
abbrev succDegreeRootCrossingTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCrossingNonnegStatement

/-- Challenge-facing equivalence between the same-degree slot-data target and
the repaired same-degree pair endpoint. -/
theorem sameDegreeSlotDataTarget_iff_pairTarget :
    sameDegreeSlotDataTarget ↔ sameDegreePairTarget :=
  posComboNoCommonSameDegreeSlotData_iff_pairHasCommonInterleaver

/-- Challenge-facing reduction from same-degree slot data to the repaired
same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_slotData
    (hslot : sameDegreeSlotDataTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_slotData hslot

/-- Challenge-facing reduction from same-degree root crossing to slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCrossing
    (hcross : sameDegreeRootCrossingTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCrossing hcross

/-- Challenge-facing reduction from same-degree root crossing to the repaired
same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCrossing
    (hcross : sameDegreeRootCrossingTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hcross

/-- Challenge-facing reduction from the same-degree orientation alternative to
same-degree root crossing. -/
theorem sameDegreeRootCrossingTarget_of_orientationAlternative
    (horient : sameDegreeOrientationAlternativeTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_orientationAlternative horient

/-- Challenge-facing reduction from the same-degree orientation alternative to
the repaired same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_orientationAlternative
    (horient : sameDegreeOrientationAlternativeTarget) :
    sameDegreePairTarget :=
  posComboNoCommonSameDegreePairHasCommonInterleaver_of_orientationAlternative_nonneg
    horient

/-- Challenge-facing equivalence between the succ-degree slot-data target and
the repaired succ-degree pair endpoint. -/
theorem succDegreeSlotDataTarget_iff_pairTarget :
    succDegreeSlotDataTarget ↔ succDegreePairTarget :=
  posComboNoCommonSuccDegreeSlotData_iff_pairHasCommonInterleaver

/-- Challenge-facing reduction from succ-degree slot data to the repaired
succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_slotData
    (hslot : succDegreeSlotDataTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_slotData hslot

/-- Challenge-facing reduction from the fixed succ-degree orientation to
succ-degree root crossing. -/
theorem succDegreeRootCrossingTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_orientation horient

/-- Challenge-facing reduction from left splitting and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_leftSplits_and_rootCrossing
    (hsplit : succDegreeLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing hsplit hcross

/-- Challenge-facing reduction from left splitting and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_leftSplits_and_rootCrossing
    (hsplit : succDegreeLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    hsplit hcross

/-- Challenge-facing PF/ASW reduction to the succ-degree left-splitting target. -/
theorem succDegreeLeftSplitsTarget_of_forward_asw
    (hASW : forwardASWTarget) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW

/-- Challenge-facing PF/ASW reduction to the residual left-splitting target. -/
theorem succDegreeResidualLeftSplitsTarget_of_forward_asw
    (hASW : forwardASWTarget) :
    succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw hASW

/-- The zero-aware ASW target is equivalent to the splitting-only target. -/
theorem forwardASWTarget_iff_splitsTarget :
    forwardASWTarget ↔ forwardASWSplitsTarget :=
  aissenSchoenbergWhitneyForwardOrZero_iff_splits

/-- Challenge-facing bridge from splitting-only ASW to the zero-aware ASW
target. -/
theorem forwardASWTarget_of_splitsTarget
    (hASW : forwardASWSplitsTarget) :
    forwardASWTarget :=
  aissenSchoenbergWhitneyForwardOrZero_of_splits hASW

/-- Challenge-facing PF/ASW reduction to the succ-degree left-splitting target,
using only the splitting conjunct of ASW. -/
theorem succDegreeLeftSplitsTarget_of_forward_asw_splits
    (hASW : forwardASWSplitsTarget) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw_splits hASW

/-- Challenge-facing PF/ASW reduction to the residual left-splitting target,
using only the splitting conjunct of ASW. -/
theorem succDegreeResidualLeftSplitsTarget_of_forward_asw_splits
    (hASW : forwardASWSplitsTarget) :
    succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw_splits hASW

/-- Challenge-facing reduction from the residual constant-coefficient branch to
the full succ-degree left-splitting target. -/
theorem succDegreeLeftSplitsTarget_of_residual
    (hres : succDegreeResidualLeftSplitsTarget) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_residual hres

/-- Challenge-facing equivalence between the full succ-degree left-splitting
target and its residual constant-coefficient branch. -/
theorem succDegreeLeftSplitsTarget_iff_residual :
    succDegreeLeftSplitsTarget ↔ succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_iff_residual

/-- Challenge-facing reduction from forward ASW and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_and_rootCrossing
    (hASW : forwardASWTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from splitting-only ASW and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_splits_and_rootCrossing
    (hASW : forwardASWSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from forward ASW and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_and_rootCrossing
    (hASW : forwardASWTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from splitting-only ASW and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_splits_and_rootCrossing
    (hASW : forwardASWSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from the residual branch and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_residual_and_rootCrossing
    (hres : succDegreeResidualLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairTarget_of_leftSplits_and_rootCrossing
    (succDegreeLeftSplitsTarget_of_residual hres) hcross

/-- Challenge-facing reduction from left splitting and fixed orientation to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_leftSplits_and_orientation
    (hsplit : succDegreeLeftSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_orientation hsplit horient

/-- Challenge-facing reduction from left splitting and fixed orientation to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_leftSplits_and_orientation
    (hsplit : succDegreeLeftSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_orientation
    hsplit horient

/-- Challenge-facing reduction from forward ASW and fixed orientation to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_and_orientation
    (hASW : forwardASWTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_orientation
    hASW horient

/-- Challenge-facing reduction from splitting-only ASW and fixed orientation to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_splits_and_orientation
    (hASW : forwardASWSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_orientation
    hASW horient

/-- Challenge-facing reduction from forward ASW and fixed orientation to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_and_orientation
    (hASW : forwardASWTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_orientation
    hASW horient

/-- Challenge-facing reduction from splitting-only ASW and fixed orientation to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_splits_and_orientation
    (hASW : forwardASWSplitsTarget)
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_splits_and_orientation
    hASW horient

/-- Challenge-facing reduction from the stronger fixed orientation to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_orientation_nonneg
    horient

/-- Challenge-facing reduction from the affine-family bridge to the repaired
succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_affineFamily
    (haff : PosComboNoCommonAffineFamilyStatement) :
    succDegreePairTarget :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haff

/-- Challenge-facing no-common left-endpoint reduction from the affine-family
bridge.  This is the endpoint part of `succDegreePairTarget_of_affineFamily`;
the remaining input is producing the affine family from positive
compatibility. -/
theorem succDegreeNoCommonLeftSplitsTarget_of_affineFamily
    (haff : PosComboNoCommonAffineFamilyStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    f.Splits :=
  posComboNoCommonSuccDegreeLeftSplits_of_affineFamily
    haff hf_pos hg_pos hfnn hgnn hfg hsucc hno

/-- Challenge-facing no-common left-endpoint reduction from boundary-right
pair orientation. -/
theorem succDegreeNoCommonLeftSplitsTarget_of_boundaryRight
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    f.Splits :=
  posComboNoCommonSuccDegreeLeftSplits_of_boundaryRightPairOrientation
    hboundary hf_pos hg_pos hfnn hgnn hfg hsucc hno

/-- Challenge-facing reduction from the boundary-right-pair orientation
statement to the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_boundaryRight
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
    hboundary

/-- Full roadmap reduction for the common-left target. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal : _root_.RealRooted.CommonLeftInterleaverFamilyUpgradeStatement) :
    commonLeftInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    htwo hglobal

/-- Direct roadmap reduction for the common-left target after the finite-family
common-left upgrade has been internalized. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge_direct
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement) :
    commonLeftInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    htwo

/-- Full roadmap reduction for the common-right target. -/
theorem commonInterleaverTarget_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    commonInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge htwo

/-- Challenge-facing full roadmap reduction from the root-crossing formulations,
with the succ-degree left endpoint supplied by forward ASW. -/
theorem commonInterleaverTarget_of_rootCrossing_and_forward_asw
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : forwardASWTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forward_asw
    hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the repaired same-degree/succ-degree no-common pair bridges. -/
theorem commonInterleaverNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the honest degree-split package. -/
theorem commonInterleaverNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the boundary-right-pair orientation statement. -/
theorem commonInterleaverNonnegCoeffsTarget_of_boundaryRight
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
    hboundary

/-- Challenge-facing projection from the nonnegative four-way package target
to the nonnegative common-right interleaver target. -/
theorem commonInterleaverNonnegCoeffsTarget_of_fourWay
    (hfour : fourWayNonnegCoeffsTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    hfour

/-- Challenge-facing projection from the nonnegative-coefficient common-right
interleaver target to the finite-family compatibility target. -/
theorem familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (hcommon : commonInterleaverNonnegCoeffsTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    hcommon

/-- Challenge-facing projection from the nonnegative four-way package target
to the nonnegative finite-family compatibility target. -/
theorem familyCompatibleNonnegCoeffsTarget_of_fourWay
    (hfour : fourWayNonnegCoeffsTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_fourWay hfour)

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the repaired same-degree/succ-degree no-common pair
bridges. -/
theorem familyCompatibleNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_pairDegreeSplit hsame hsucc)

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the honest degree-split package. -/
theorem familyCompatibleNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_degreeSplit hsame hsucc)

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the boundary-right-pair orientation statement. -/
theorem familyCompatibleNonnegCoeffsTarget_of_boundaryRight
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (commonInterleaverNonnegCoeffsTarget_of_boundaryRight hboundary)

/-- Challenge-facing reduction for the nonnegative four-way package target
from the repaired same-degree/succ-degree no-common pair bridges. -/
theorem fourWayNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative four-way package target
from the honest degree-split package. -/
theorem fourWayNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_degreeSplit_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative four-way package target
from the boundary-right-pair orientation statement. -/
theorem fourWayNonnegCoeffsTarget_of_boundaryRight
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_boundaryRight_nonneg hboundary

/-- Challenge-facing four-way package from the natural two-polynomial bridge. -/
theorem fourWay_of_pairBridge
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos hrr hpos htwo

/-- Solved low-degree four-way Chudnovsky--Seymour package. -/
theorem fourWay_of_natDegree_le_one {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_natDegree_le_one
    (fs := fs) hpos hdeg

/-- Solved low-degree pairwise/common-interleaver equivalence. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one
    hpos hdeg

/-- Solved low-degree pairwise/full-family compatibility equivalence. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  RealRooted.pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing reduction for the left-oriented common-interleaver target. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal : PairwiseHasCommonLeftInterleaver fs → HasCommonLeftInterleaver fs) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    hpos htwo hglobal

/-- Challenge-facing direct left-oriented finite-family reduction after the
common-left upgrade: only the two-polynomial common-left bridge remains. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    hrr hpos htwo

end ChudnovskySeymour
end Challenges
end RealRooted
