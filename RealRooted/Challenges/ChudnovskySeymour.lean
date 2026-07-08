import RealRooted.ChudnovskySeymour
import RealRooted.CommonInterleaverExamples
import RealRooted.CommonInterleaverSeq
import RealRooted.SuccDegreeRootCrossing
import RealRooted.Bezoutian
import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeQuadraticObstruction
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.SuccDegreeLeftEndpoint
import RealRooted.RootContinuity
import RealRooted.RootCountJump
import RealRooted.DegreeDropReversal
import RealRooted.DegreeDropDivXPrec

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

/-- Roadmap target for pairwise compatibility versus full finite-family
compatibility under the standard hypotheses. -/
abbrev familyCompatibleTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target

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

/-- Same-degree analytic root-count subtarget for milestone B1. -/
abbrev sameDegreeRootCountTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountNonnegStatement

/-- Cubic partial-separation leaf for the same-degree root-count route. -/
abbrev sameDegreeCubicSecondRootBoundTarget : Prop :=
  CubicSecondRootBoundStatement

/-- Interior `2`-below cubic partial-separation leaf. -/
abbrev sameDegreeCubicInteriorTwoBelowTarget : Prop :=
  CubicInteriorTwoBelowStatement

/-- Interior `2`-above cubic partial-separation leaf. -/
abbrev sameDegreeCubicInteriorTwoAboveTarget : Prop :=
  CubicInteriorTwoAboveStatement

/-- Pure algebraic negative-discriminant leaf for the `2`-below monic cubic
pencil. -/
abbrev sameDegreeCubicDiscrPencilNegTwoBelowTarget : Prop :=
  CubicDiscrMonicPencilNegTwoBelowStatement

/-- Pure algebraic negative-discriminant leaf for the `2`-above monic cubic
pencil. -/
abbrev sameDegreeCubicDiscrPencilNegTwoAboveTarget : Prop :=
  CubicDiscrMonicPencilNegTwoAboveStatement

/-- Challenge-facing discriminant bridge for the cubic interior route.  A
positive-combination real-rooted split cubic pair gives nonnegative
discriminant along its monic root pencil. -/
theorem sameDegreeCubicDiscrPencilNonnegTarget
    {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hfs : f.Splits) (hgs : g.Splits)
    (hfd : f.natDegree = 3) (hgd : g.natDegree = 3)
    (hpc : PosComboRealRooted f g)
    (a b c p q r : ℝ)
    (hfr : f.roots = {a, b, c}) (hgr : g.roots = {p, q, r}) :
    ∀ s : ℝ, 0 < s →
      0 ≤ cubicDiscr ((X - C a) * (X - C b) * (X - C c)
        + C s * ((X - C p) * (X - C q) * (X - C r))) :=
  cubicDiscr_monicPencil_nonneg_of_posCombo
    hf hg hfs hgs hfd hgd hpc a b c p q r hfr hgr

/-- Challenge-facing reduction from the `2`-below negative-discriminant leaf to
the interior obstruction. -/
theorem sameDegreeCubicInteriorTwoBelowTarget_of_discrPencilNeg
    (hneg : sameDegreeCubicDiscrPencilNegTwoBelowTarget) :
    sameDegreeCubicInteriorTwoBelowTarget :=
  cubicInteriorTwoBelow_of_discr_monicPencil_neg hneg

/-- Challenge-facing reduction from the `2`-above negative-discriminant leaf to
the interior obstruction. -/
theorem sameDegreeCubicInteriorTwoAboveTarget_of_discrPencilNeg
    (hneg : sameDegreeCubicDiscrPencilNegTwoAboveTarget) :
    sameDegreeCubicInteriorTwoAboveTarget :=
  cubicInteriorTwoAbove_of_discr_monicPencil_neg hneg

/-- Challenge-facing reduction from the two pure negative-discriminant leaves
to the cubic second-root bound. -/
theorem sameDegreeCubicSecondRootBoundTarget_of_discrPencilNeg
    (hbelow : sameDegreeCubicDiscrPencilNegTwoBelowTarget)
    (habove : sameDegreeCubicDiscrPencilNegTwoAboveTarget) :
    sameDegreeCubicSecondRootBoundTarget :=
  cubicSecondRootBound_of_discr_monicPencil_neg hbelow habove

/-- Challenge-facing reduction from the normalized negative-discriminant leaves
to the cubic second-root bound. -/
theorem sameDegreeCubicSecondRootBoundTarget_of_normalized
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0) :
    sameDegreeCubicSecondRootBoundTarget :=
  cubicSecondRootBound_of_normalized hbelow habove

/-- Same-degree upper-threshold root-count subtarget for milestone B1. -/
abbrev sameDegreeRootCountAboveTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountAboveNonnegStatement

/-- Same-degree lower root-count subtarget restricted to common non-root
thresholds. -/
abbrev sameDegreeRootCountNonRootTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement

/-- Same-degree upper root-count subtarget restricted to common non-root
thresholds. -/
abbrev sameDegreeRootCountAboveNonRootTarget : Prop :=
  PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement

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



/-- No-common orientation target used before splitting into same-degree and
successor-degree endpoint repairs. -/
abbrev noCommonOrientationTarget : Prop :=
  PosComboNoCommonOrientationStatement

/-- All-combinations bridge target implying the no-common orientation target. -/
abbrev allComboBridgeTarget : Prop :=
  PosComboNoCommonToAllComboBridgeStatement

/-- Affine-family bridge target for packaging the no-common nonnegative
positive-combination hypotheses into Branden's affine-family input. -/
abbrev affineFamilyTarget : Prop :=
  PosComboNoCommonAffineFamilyStatement

/-- Boundary-right-pair orientation target; this is a stronger sufficient
condition for the affine-family bridge. -/
abbrev boundaryRightPairOrientationTarget : Prop :=
  PosComboNoCommonBoundaryRightPairOrientationStatement

/-- Succ-degree root-slot reformulation of milestone B2. -/
abbrev succDegreeSlotDataTarget : Prop :=
  PosComboNoCommonSuccDegreeSlotDataNonnegStatement

/-- Succ-degree descending-root crossing subtarget for milestone B2. -/
abbrev succDegreeRootCrossingTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCrossingNonnegStatement

/-- Two-polynomial common-left bridge target: compatibility implies a common left interleaver. -/
def compatiblePairHasCommonLeftInterleaverTarget : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    ∃ h : ℝ[X], Prec h f ∧ Prec h g

/-- Succ-degree analytic root-count subtarget for milestone B2. -/
abbrev succDegreeRootCountTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountNonnegStatement

/-- Succ-degree upper-threshold root-count subtarget for milestone B2. -/
abbrev succDegreeRootCountAboveTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement

/-- Succ-degree upper-threshold root-count subtarget restricted to common
non-root thresholds. -/
abbrev succDegreeRootCountAboveNonRootTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement

/-- Compatible-pair version of the succ-degree common-non-root upper
root-count leaf. -/
abbrev compatibleSuccDegreeRootCountAboveNonRootTarget : Prop :=
  CompatibleSuccDegreeRootCountAboveNonRootStatement

/-- Compatible-pair gap-at-most-two version of the succ-degree common-non-root
upper root-count leaf. -/
abbrev compatibleSuccDegreeRootCountAboveLeTwoTarget : Prop :=
  CompatibleSuccDegreeRootCountAboveLeTwoStatement

/-- Exact gap-two obstruction for the compatible succ-degree common-non-root
upper root-count leaf. -/
abbrev compatibleSuccDegreeRootCountAboveNoGapTwoTarget : Prop :=
  CompatibleSuccDegreeRootCountAboveNoGapTwoStatement

/-- Closed-segment exact gap-two obstruction for the compatible succ-degree
common-non-root upper root-count leaf. -/
abbrev compatibleSuccDegreeClosedSegmentNoGapTwoTarget : Prop :=
  CompatibleSuccDegreeClosedSegmentNoGapTwoStatement

/-- Closed-segment endpoint count equality for the compatible succ-degree
common-non-root upper root-count leaf. -/
abbrev compatibleSuccDegreeClosedSegmentCountEqTarget : Prop :=
  CompatibleSuccDegreeClosedSegmentCountEqStatement

/-- Right-pencil exact gap-two obstruction for the compatible succ-degree
common-non-root upper root-count leaf. -/
abbrev compatibleSuccDegreeRightFamilyNoGapTwoTarget : Prop :=
  CompatibleSuccDegreeRightFamilyNoGapTwoStatement

/-- Endpoint-sign exact gap-two obstruction for the compatible succ-degree
common-non-root upper root-count leaf. -/
abbrev compatibleSuccDegreeEndpointSignNoGapTwoTarget : Prop :=
  CompatibleSuccDegreeEndpointSignNoGapTwoStatement

/-- Coefficient-free compatible succ-degree all-combinations target.

This target is now known to be false; see
`not_compatibleSuccDegreeAllComboTarget`. -/
abbrev compatibleSuccDegreeAllComboTarget : Prop :=
  CompatibleSuccDegreeAllComboStatement

/-- Challenge-facing falsity of the coefficient-free all-combinations shortcut.
The counterexample is formalized in `RealRooted.CommonInterleaverExamples`. -/
theorem not_compatibleSuccDegreeAllComboTarget :
    ¬ compatibleSuccDegreeAllComboTarget :=
  CommonInterleaverExamples.not_compatibleSuccDegreeAllComboStatement

/-- Signed right-pencil form of the compatible succ-degree all-combinations
target.

This target is now known to be false; see
`not_compatibleSuccDegreeSignedRightFamilyTarget`. -/
abbrev compatibleSuccDegreeSignedRightFamilyTarget : Prop :=
  CompatibleSuccDegreeSignedRightFamilyStatement

/-- Challenge-facing falsity of the signed right-pencil shortcut. -/
theorem not_compatibleSuccDegreeSignedRightFamilyTarget :
    ¬ compatibleSuccDegreeSignedRightFamilyTarget :=
  CommonInterleaverExamples.not_compatibleSuccDegreeSignedRightFamilyStatement

/-- Negative right-pencil form of the compatible succ-degree all-combinations
target.

This target is now known to be false; see
`not_compatibleSuccDegreeNegativeRightFamilyTarget`. -/
abbrev compatibleSuccDegreeNegativeRightFamilyTarget : Prop :=
  CompatibleSuccDegreeNegativeRightFamilyStatement

/-- Challenge-facing falsity of the coefficient-free negative right-pencil
shortcut. -/
theorem not_compatibleSuccDegreeNegativeRightFamilyTarget :
    ¬ compatibleSuccDegreeNegativeRightFamilyTarget :=
  CommonInterleaverExamples.not_compatibleSuccDegreeNegativeRightFamilyStatement

/-- Nonnegative-coefficient negative right-pencil form of the compatible
succ-degree all-combinations target.

This target is now known to be false; see
`not_compatibleSuccDegreeNegativeRightFamilyNonnegTarget`. -/
abbrev compatibleSuccDegreeNegativeRightFamilyNonnegTarget : Prop :=
  CompatibleSuccDegreeNegativeRightFamilyNonnegStatement

/-- Challenge-facing falsity of the nonnegative-coefficient negative
right-pencil shortcut.  The counterexample is `f = X + 1`,
`g = (X + 2) * (X + 3)`, formalized in
`RealRooted.CommonInterleaverExamples`. -/
theorem not_compatibleSuccDegreeNegativeRightFamilyNonnegTarget :
    ¬ compatibleSuccDegreeNegativeRightFamilyNonnegTarget :=
  CommonInterleaverExamples.not_compatibleSuccDegreeNegativeRightFamilyNonnegStatement

/-- Coefficient-free compatible succ-degree orientation target.

This target is now known to be false; see
`not_compatibleSuccDegreePrecTarget`. -/
abbrev compatibleSuccDegreePrecTarget : Prop :=
  CompatibleSuccDegreePrecStatement

/-- Challenge-facing falsity of the forced compatible succ-degree `Prec`
shortcut. -/
theorem not_compatibleSuccDegreePrecTarget :
    ¬ compatibleSuccDegreePrecTarget :=
  CommonInterleaverExamples.not_compatibleSuccDegreePrecStatement

/-- Exact lower-threshold endpoint-sign count comparison for the compatible
succ-degree common-non-root upper root-count leaf. -/
abbrev compatibleSuccDegreeEndpointSignLowerCountEqTarget : Prop :=
  CompatibleSuccDegreeEndpointSignLowerCountEqStatement

/-- Lower-threshold endpoint-sign exact gap obstruction for the compatible
succ-degree common-non-root upper root-count leaf. -/
abbrev compatibleSuccDegreeEndpointSignLowerNoGapTarget : Prop :=
  CompatibleSuccDegreeEndpointSignLowerNoGapStatement

/-- Degree-two succ-degree root-order leaf for the remaining exact no-gap
obstruction. -/
abbrev succDegreeQuadraticCubicRootBoundsTarget : Prop :=
  SuccDegreeQuadraticCubicRootBoundsStatement

/-- Degree-two succ-degree obstruction to the first-above configuration. -/
abbrev succDegreeQuadraticCubicFirstAboveObstructionTarget : Prop :=
  SuccDegreeQuadraticCubicFirstAboveObstructionStatement

/-- Degree-two succ-degree obstruction to the second-above configuration. -/
abbrev succDegreeQuadraticCubicSecondAboveObstructionTarget : Prop :=
  SuccDegreeQuadraticCubicSecondAboveObstructionStatement

/-- Degree-two succ-degree obstruction to the full-below configuration. -/
abbrev succDegreeQuadraticCubicFullBelowObstructionTarget : Prop :=
  SuccDegreeQuadraticCubicFullBelowObstructionStatement

/-- Pure monic-pencil obstruction for the first-above quadratic/cubic
configuration. -/
abbrev quadraticCubicFirstAbovePencilObstructionTarget : Prop :=
  QuadraticCubicFirstAbovePencilObstructionStatement

/-- Pure monic-pencil obstruction for the second-above quadratic/cubic
configuration. -/
abbrev quadraticCubicSecondAbovePencilObstructionTarget : Prop :=
  QuadraticCubicSecondAbovePencilObstructionStatement

/-- Pure monic-pencil obstruction for the full-below quadratic/cubic
configuration. -/
abbrev quadraticCubicFullBelowPencilObstructionTarget : Prop :=
  QuadraticCubicFullBelowPencilObstructionStatement

/-- Challenge-facing reduction from the three quadratic/cubic obstruction
leaves to the degree-two root-order leaf. -/
theorem succDegreeQuadraticCubicRootBoundsTarget_of_obstructions
    (hfirst : succDegreeQuadraticCubicFirstAboveObstructionTarget)
    (hsecond : succDegreeQuadraticCubicSecondAboveObstructionTarget)
    (hbelow : succDegreeQuadraticCubicFullBelowObstructionTarget) :
    succDegreeQuadraticCubicRootBoundsTarget :=
  succDegreeQuadraticCubicRootBounds_of_obstructions hfirst hsecond hbelow

/-- Challenge-facing reduction from the pure first-above monic-pencil
obstruction to the polynomial obstruction leaf. -/
theorem succDegreeQuadraticCubicFirstAboveObstructionTarget_of_pencil
    (hpencil : quadraticCubicFirstAbovePencilObstructionTarget) :
    succDegreeQuadraticCubicFirstAboveObstructionTarget :=
  succDegreeQuadraticCubicFirstAboveObstruction_of_pencil hpencil

/-- Challenge-facing reduction from the pure second-above monic-pencil
obstruction to the polynomial obstruction leaf. -/
theorem succDegreeQuadraticCubicSecondAboveObstructionTarget_of_pencil
    (hpencil : quadraticCubicSecondAbovePencilObstructionTarget) :
    succDegreeQuadraticCubicSecondAboveObstructionTarget :=
  succDegreeQuadraticCubicSecondAboveObstruction_of_pencil hpencil

/-- Challenge-facing reduction from the pure full-below monic-pencil
obstruction to the polynomial obstruction leaf. -/
theorem succDegreeQuadraticCubicFullBelowObstructionTarget_of_pencil
    (hpencil : quadraticCubicFullBelowPencilObstructionTarget) :
    succDegreeQuadraticCubicFullBelowObstructionTarget :=
  succDegreeQuadraticCubicFullBelowObstruction_of_pencil hpencil

/-- Challenge-facing reduction from the three pure monic-pencil obstructions
to the degree-two root-order leaf. -/
theorem succDegreeQuadraticCubicRootBoundsTarget_of_pencil_obstructions
    (hfirst : quadraticCubicFirstAbovePencilObstructionTarget)
    (hsecond : quadraticCubicSecondAbovePencilObstructionTarget)
    (hbelow : quadraticCubicFullBelowPencilObstructionTarget) :
    succDegreeQuadraticCubicRootBoundsTarget :=
  succDegreeQuadraticCubicRootBounds_of_pencil_obstructions
    hfirst hsecond hbelow

/-- Succ-degree lower-threshold root-count subtarget restricted to common
non-root thresholds. -/
abbrev succDegreeRootCountNonRootTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement

/-- Succ-degree common-left-interleaver formulation for the honest
common-non-root root-count leaf. -/
abbrev succDegreeCommonLeftInterleaverTarget : Prop :=
  PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement

/-- Succ-degree residual constant-term root-count branch. -/
abbrev succDegreeRootCountResidualTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountResidualNonnegStatement

/-- Exact residual orientation subtarget for the succ-degree residual branch.
This target is now known to be false; see
`not_succDegreeRootCountResidualPrecTarget`. -/
abbrev succDegreeRootCountResidualPrecTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountResidualPrecStatement

/-- Challenge-facing falsity of the residual `Prec` shortcut.  The counterexample
is `f = X`, `g = (X + 1) * (X + 2)`, formalized in
`RealRooted.CommonInterleaverExamples`. -/
theorem not_succDegreeRootCountResidualPrecTarget :
    ¬ succDegreeRootCountResidualPrecTarget :=
  CommonInterleaverExamples.not_posComboNoCommonSuccDegreeRootCountResidualPrecStatement

/-- Succ-degree nonzero constant-term root-count branch. -/
abbrev succDegreeRootCountLeadTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountLeadNonnegStatement

/-- Succ-degree lead root-count branch with both constant terms nonzero. -/
abbrev succDegreeRootCountLeadBothNonzeroTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonnegStatement

/-- Succ-degree lead root-count branch with zero higher-degree constant term. -/
abbrev succDegreeRootCountLeadRightZeroTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountLeadRightZeroNonnegStatement

/-- Exact `divX` orientation subtarget for the right-zero lead branch. -/
abbrev succDegreeRootCountLeadRightZeroDivXPrecTarget : Prop :=
  PosComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrecStatement

/-- Sharper right-zero lead branch orientation target: prove the original
succ-degree orientation `Prec f g` before applying the `divX` degree-drop
reduction. -/
abbrev succDegreeRootCountLeadRightZeroPrecTarget : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    f.coeff 0 ≠ 0 →
    g.coeff 0 = 0 →
    Prec f g

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

/-- Challenge-facing reduction from same-degree root counts to same-degree
root crossing. -/
theorem sameDegreeRootCrossingTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCount hcount

/-- Challenge-facing reduction from same-degree upper-threshold root counts to
same-degree root crossing. -/
theorem sameDegreeRootCrossingTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hcount

/-- Challenge-facing reduction from same-degree root crossing to the
lower-threshold root-count formulation. -/
theorem sameDegreeRootCountTarget_of_rootCrossing
    (hcross : sameDegreeRootCrossingTarget) :
    sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCount_of_rootCrossing hcross

/-- Challenge-facing conversion from same-degree upper-threshold root counts to
the lower-threshold formulation. -/
theorem sameDegreeRootCountTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCount_of_rootCountAbove hcount

/-- Challenge-facing conversion from same-degree lower-threshold root counts to
the upper-threshold formulation. -/
theorem sameDegreeRootCountAboveTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreeRootCountAboveTarget :=
  posComboNoCommonSameDegreeRootCountAbove_of_rootCount hcount

/-- Challenge-facing equivalence between same-degree upper and lower
root-count formulations. -/
theorem sameDegreeRootCountAboveTarget_iff_rootCount :
    sameDegreeRootCountAboveTarget ↔ sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCountAbove_iff_rootCount

/-- Challenge-facing equivalence between same-degree root crossing and the
lower root-count formulation. -/
theorem sameDegreeRootCrossingTarget_iff_rootCount :
    sameDegreeRootCrossingTarget ↔ sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCrossing_iff_rootCount

/-- Challenge-facing equivalence between same-degree root crossing and the
upper root-count formulation. -/
theorem sameDegreeRootCrossingTarget_iff_rootCountAbove :
    sameDegreeRootCrossingTarget ↔ sameDegreeRootCountAboveTarget :=
  posComboNoCommonSameDegreeRootCrossing_iff_rootCountAbove

/-- Challenge-facing reduction from common-non-root same-degree lower root
counts to the full lower-threshold formulation. -/
theorem sameDegreeRootCountTarget_of_nonRoot
    (hcount : sameDegreeRootCountNonRootTarget) :
    sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCount_of_nonRoot hcount

/-- Challenge-facing reduction from common-non-root same-degree upper root
counts to the full upper-threshold formulation. -/
theorem sameDegreeRootCountAboveTarget_of_nonRoot
    (hcount : sameDegreeRootCountAboveNonRootTarget) :
    sameDegreeRootCountAboveTarget :=
  posComboNoCommonSameDegreeRootCountAbove_of_nonRoot hcount

/-- Challenge-facing equivalence between the same-degree upper and lower
common-non-root root-count formulations. -/
theorem sameDegreeRootCountAboveNonRootTarget_iff_rootCountNonRoot :
    sameDegreeRootCountAboveNonRootTarget ↔ sameDegreeRootCountNonRootTarget :=
  posComboNoCommonSameDegreeRootCountAboveNonRoot_iff_rootCountNonRoot

/-- Challenge-facing reduction from common-non-root same-degree lower root
counts to the full upper-threshold formulation. -/
theorem sameDegreeRootCountAboveTarget_of_rootCountNonRoot
    (hcount : sameDegreeRootCountNonRootTarget) :
    sameDegreeRootCountAboveTarget :=
  posComboNoCommonSameDegreeRootCountAbove_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from common-non-root same-degree upper root
counts to the full lower-threshold formulation. -/
theorem sameDegreeRootCountTarget_of_rootCountAboveNonRoot
    (hcount : sameDegreeRootCountAboveNonRootTarget) :
    sameDegreeRootCountTarget :=
  posComboNoCommonSameDegreeRootCount_of_rootCountAboveNonRoot hcount

/-- Challenge-facing reduction from common-non-root same-degree lower root
counts to same-degree root crossing. -/
theorem sameDegreeRootCrossingTarget_of_rootCountNonRoot
    (hcount : sameDegreeRootCountNonRootTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from common-non-root same-degree upper root
counts to same-degree root crossing. -/
theorem sameDegreeRootCrossingTarget_of_rootCountAboveNonRoot
    (hcount : sameDegreeRootCountAboveNonRootTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hcount

/-- Challenge-facing reduction from same-degree root counts to slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCount hcount

/-- Challenge-facing reduction from same-degree upper-threshold root counts to
slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCountAbove hcount

/-- Challenge-facing reduction from common-non-root same-degree lower root
counts to slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCountNonRoot
    (hcount : sameDegreeRootCountNonRootTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from common-non-root same-degree upper root
counts to slot data. -/
theorem sameDegreeSlotDataTarget_of_rootCountAboveNonRoot
    (hcount : sameDegreeRootCountAboveNonRootTarget) :
    sameDegreeSlotDataTarget :=
  posComboNoCommonSameDegreeSlotData_of_rootCountAboveNonRoot hcount

/-- Challenge-facing reduction from same-degree root counts to the repaired
same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCount
    (hcount : sameDegreeRootCountTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hcount

/-- Challenge-facing reduction from same-degree upper-threshold root counts to
the repaired same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCountAbove
    (hcount : sameDegreeRootCountAboveTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hcount

/-- Challenge-facing reduction from common-non-root same-degree lower root
counts to the repaired same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCountNonRoot
    (hcount : sameDegreeRootCountNonRootTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from common-non-root same-degree upper root
counts to the repaired same-degree pair endpoint. -/
theorem sameDegreePairTarget_of_rootCountAboveNonRoot
    (hcount : sameDegreeRootCountAboveNonRootTarget) :
    sameDegreePairTarget :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hcount

/-- Challenge-facing right-pencil parity bridge for same-degree lower root
counts. -/
theorem sameDegreeRootCount_oddDiff_iff_pencilCrossing
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  posComboSameDegree_odd_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hxf hxg

/-- Challenge-facing right-pencil parity bridge for same-degree upper root
counts. -/
theorem sameDegreeRootCountAbove_oddDiff_iff_pencilCrossing
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  posComboSameDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hxf hxg

/-- Challenge-facing reduction from the same-degree orientation alternative to
same-degree root crossing. -/
theorem sameDegreeRootCrossingTarget_of_orientationAlternative
    (horient : sameDegreeOrientationAlternativeTarget) :
    sameDegreeRootCrossingTarget :=
  posComboNoCommonSameDegreeRootCrossing_of_orientationAlternative horient

/-- Challenge-facing low-degree base case for the same-degree root-crossing
inequalities. -/
theorem sameDegreeRootCrossingPair_of_natDegree_le_one
    {f g : ℝ[X]} (hf_deg_le_one : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  sameDegreeRootCrossing_of_natDegree_le_one hf_deg_le_one

/-- Challenge-facing low-degree base case for the same-degree root-count
formulation. -/
theorem sameDegreeRootCountPair_of_natDegree_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 :=
  rootCount_diff_le_one_of_natDegree_le_one hf hg hdeg hf_deg_le_one x

/-- Challenge-facing low-degree base case for the upper-threshold same-degree
root-count formulation. -/
theorem sameDegreeRootCountAbovePair_of_natDegree_le_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_diff_le_one_of_natDegree_le_one hf hg hdeg hf_deg_le_one x

/-- Challenge-facing degree-two base case for the same-degree root-count
formulation in the positive-combination setting. -/
theorem sameDegreeRootCountPair_of_posCombo_natDegree_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg2 : f.natDegree = 2)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  exact rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
    hf_pos hg_pos hfg hdeg hf_deg2 x

/-- Challenge-facing cubic intermediate: in the same-degree cubic
positive-combination setting, lower-threshold root counts differ by at most
two.  This is weaker than the final same-degree root-count target, but it is a
checked next step after ruling out full cubic separation. -/
theorem sameDegreeRootCountPair_le_two_of_posCombo_natDegree_eq_three
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg3 : f.natDegree = 3)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 2 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_deg3 : g.natDegree = 3 := by rw [hdeg, hf_deg3]
  exact sameDegree_cubic_rootCount_le_two
    hf_deg3 hg_deg3 hf_split hg_split hf_pos hg_pos hfg x

/-- Challenge-facing cubic reduction: the partial-separation leaf upgrades the
same-degree cubic root-count bound from `≤ 2` to the target `≤ 1`. -/
theorem sameDegreeRootCountPair_of_secondRootBound_natDegree_eq_three
    (hbound : sameDegreeCubicSecondRootBoundTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg3 : f.natDegree = 3)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 := by
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_deg3 : g.natDegree = 3 := by rw [hdeg, hf_deg3]
  exact sameDegree_cubic_rootCount_le_one_of_secondRootBound hbound
    hf_deg3 hg_deg3 hf_split hg_split hf_pos hg_pos hfg x

/-- Challenge-facing reduction from the two interior cubic leaves to the
partial-separation leaf. -/
theorem sameDegreeCubicSecondRootBoundTarget_of_interior
    (hbelow : sameDegreeCubicInteriorTwoBelowTarget)
    (habove : sameDegreeCubicInteriorTwoAboveTarget) :
    sameDegreeCubicSecondRootBoundTarget :=
  cubicSecondRootBound_of_interior hbelow habove

/-- Challenge-facing cubic reduction from the two interior leaves to the
same-degree root-count target. -/
theorem sameDegreeRootCountPair_of_interior_natDegree_eq_three
    (hbelow : sameDegreeCubicInteriorTwoBelowTarget)
    (habove : sameDegreeCubicInteriorTwoAboveTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg3 : f.natDegree = 3)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 :=
  sameDegreeRootCountPair_of_secondRootBound_natDegree_eq_three
    (sameDegreeCubicSecondRootBoundTarget_of_interior hbelow habove)
    hf_pos hg_pos hfg hdeg hf_deg3 x

/-- Challenge-facing cubic reduction from the normalized negative-discriminant
leaves to the same-degree root-count target. -/
theorem sameDegreeRootCountPair_of_normalized_natDegree_eq_three
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg3 : f.natDegree = 3)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 :=
  sameDegree_cubic_rootCount_le_one_of_normalized_posCombo
    hbelow habove hf_pos hg_pos hfg hdeg hf_deg3 x

/-- Challenge-facing degree-two base case for the upper-threshold same-degree
root-count formulation in the positive-combination setting. -/
theorem sameDegreeRootCountAbovePair_of_posCombo_natDegree_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg2 : f.natDegree = 2)
    (x : ℝ) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  exact rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_eq_two
    hf_pos hg_pos hfg hdeg hf_deg2 x

/-- Challenge-facing degree-two base case for the same-degree root-crossing
formulation in the positive-combination setting. -/
theorem sameDegreeRootCrossingPair_of_posCombo_natDegree_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg2 : f.natDegree = 2) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  exact sameDegreeRootCrossing_of_posCombo_natDegree_eq_two
    hf_pos hg_pos hfg hdeg hf_deg2

/-- Challenge-facing degree-`≤ 2` base case for the same-degree root-count
formulation in the positive-combination/no-common setting. -/
theorem sameDegreeRootCountPair_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_two : f.natDegree ≤ 2)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 :=
  rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_two x

/-- Challenge-facing degree-`≤ 2` base case for the upper-threshold
same-degree root-count formulation in the positive-combination/no-common
setting. -/
theorem sameDegreeRootCountAbovePair_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_two : f.natDegree ≤ 2)
    (x : ℝ) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_two
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_two x

/-- Challenge-facing degree-`≤ 2` base case for the same-degree root-crossing
formulation in the positive-combination/no-common setting. -/
theorem sameDegreeRootCrossingPair_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_two : f.natDegree ≤ 2) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  sameDegreeRootCrossing_of_posCombo_natDegree_le_two
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_two

/-- Challenge-facing degree-`≤ 2` base case for the repaired same-degree
common-right-interleaver endpoint in the positive-combination/no-common
setting. -/
theorem sameDegreePairHasCommonInterleaver_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_two : f.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonSameDegreePairHasCommonInterleaver_of_natDegree_le_two
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_two

/-- Challenge-facing degree-`≤ 3` same-degree root-count route, assuming the
two cubic interior partial-separation leaves. -/
theorem sameDegreeRootCountPair_of_interior_natDegree_le_three
    (hbelow : sameDegreeCubicInteriorTwoBelowTarget)
    (habove : sameDegreeCubicInteriorTwoAboveTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_three : f.natDegree ≤ 3)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 := by
  exact rootCount_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
    hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_three x

/-- Challenge-facing degree-`≤ 3` upper-threshold route, assuming the two cubic
interior partial-separation leaves. -/
theorem sameDegreeRootCountAbovePair_of_interior_natDegree_le_three
    (hbelow : sameDegreeCubicInteriorTwoBelowTarget)
    (habove : sameDegreeCubicInteriorTwoAboveTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_three : f.natDegree ≤ 3)
    (x : ℝ) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  exact
    rootCountAbove_diff_le_one_of_posCombo_sameDegree_natDegree_le_three_of_cubicInterior
      hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_three x

/-- Challenge-facing degree-`≤ 3` root-crossing route, assuming the two cubic
interior partial-separation leaves. -/
theorem sameDegreeRootCrossingPair_of_interior_natDegree_le_three
    (hbelow : sameDegreeCubicInteriorTwoBelowTarget)
    (habove : sameDegreeCubicInteriorTwoAboveTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_three : f.natDegree ≤ 3) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  exact sameDegreeRootCrossing_of_posCombo_natDegree_le_three_of_cubicInterior
    hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_three

/-- Challenge-facing degree-`≤ 3` slot-data route from the two cubic interior
leaves. -/
theorem sameDegreeSlotDataPair_of_interior_natDegree_le_three
    (hbelow : sameDegreeCubicInteriorTwoBelowTarget)
    (habove : sameDegreeCubicInteriorTwoAboveTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_three : f.natDegree ≤ 3) :
    ∀ j, j < f.natDegree + 1 →
      ∀ (hjf : j < (rootSeqDesc f).length + 1)
        (hjg : j < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty :=
  sameDegreeSlotData_of_posCombo_natDegree_le_three_of_cubicInterior
    hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_three

/-- Challenge-facing degree-`≤ 3` repaired same-degree pair endpoint from the
two cubic interior leaves. -/
theorem sameDegreePairHasCommonInterleaver_of_interior_natDegree_le_three
    (hbelow : sameDegreeCubicInteriorTwoBelowTarget)
    (habove : sameDegreeCubicInteriorTwoAboveTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_three : f.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  sameDegreePairHasCommonInterleaver_nonneg_of_natDegree_le_three_of_cubicInterior
    hbelow habove hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_three

/-- Challenge-facing degree-`≤ 3` same-degree root-count route from the
normalized negative-discriminant leaves. -/
theorem sameDegreeRootCountPair_of_normalized_natDegree_le_three
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_three : f.natDegree ≤ 3)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 :=
  sameDegreeRootCountPair_of_interior_natDegree_le_three
    (sameDegreeCubicInteriorTwoBelowTarget_of_discrPencilNeg
      (cubicDiscrMonicPencilNegTwoBelow_of_normalized hbelow))
    (sameDegreeCubicInteriorTwoAboveTarget_of_discrPencilNeg
      (cubicDiscrMonicPencilNegTwoAbove_of_normalized habove))
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_three x

/-- Challenge-facing degree-`≤ 3` repaired same-degree pair endpoint from the
normalized negative-discriminant leaves. -/
theorem sameDegreePairHasCommonInterleaver_of_normalized_natDegree_le_three
    (hbelow : ∀ b c p r : ℝ, 1 ≤ b → b ≤ c → p ≤ 0 → 1 ≤ r →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C (1 : ℝ)) * (X - C b) * (X - C c)
          + C s * ((X - C p) * (X - C (0 : ℝ)) * (X - C r))) < 0)
    (habove : ∀ a c p q : ℝ, a ≤ 0 → 1 ≤ c → p ≤ q → q ≤ 0 →
      ∃ s : ℝ, 0 < s ∧
        cubicDiscr ((X - C a) * (X - C (1 : ℝ)) * (X - C c)
          + C s * ((X - C p) * (X - C q) * (X - C (0 : ℝ)))) < 0)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_three : f.natDegree ≤ 3) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  sameDegreePairHasCommonInterleaver_of_interior_natDegree_le_three
    (sameDegreeCubicInteriorTwoBelowTarget_of_discrPencilNeg
      (cubicDiscrMonicPencilNegTwoBelow_of_normalized hbelow))
    (sameDegreeCubicInteriorTwoAboveTarget_of_discrPencilNeg
      (cubicDiscrMonicPencilNegTwoAbove_of_normalized habove))
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_three

/-- Challenge-facing low-degree base case for the repaired same-degree
pair-interleaver endpoint. -/
theorem sameDegreePairHasCommonInterleaver_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonSameDegreePairHasCommonInterleaver_of_degree_le_one
    hf_pos hg_pos hdeg hf_deg_le_one

/-- Challenge-facing low-degree base case for same-degree root-slot data. -/
theorem sameDegreeSlotDataPair_of_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∀ j, j < f.natDegree + 1 →
      ∀ (hjf : j < (rootSeqDesc f).length + 1)
        (hjg : j < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty :=
  sameDegreeSlotData_of_natDegree_le_one
    hf_pos hg_pos hdeg hf_deg_le_one

/-- Challenge-facing degree-two obstruction: separated monic quadratic roots
contradict positive-combination real-rootedness. -/
theorem sameDegreeQuadraticSeparatedRoots_not_posCombo
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hsep : d < a) :
    ¬ PosComboRealRooted ((X - C a) * (X - C b)) ((X - C c) * (X - C d)) :=
  RealRooted.not_posComboRealRooted_quadratic_roots_separated hab hcd hsep

/-- Challenge-facing scaled degree-two obstruction for positive-leading
quadratic factors. -/
theorem sameDegreeQuadraticSeparatedRoots_not_posCombo_scaled
    {A B a b c d : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hab : a ≤ b) (hcd : c ≤ d) (hsep : d < a) :
    ¬ PosComboRealRooted
      (C A * ((X - C a) * (X - C b)))
      (C B * ((X - C c) * (X - C d))) :=
  RealRooted.not_posComboRealRooted_pos_scaled_quadratic_roots_separated
    hA hB hab hcd hsep

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

/-- Challenge-facing reduction from the fixed succ-degree orientation to
upper-threshold succ-degree root counts. -/
theorem succDegreeRootCountAboveTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_orientation horient

/-- Challenge-facing reduction from the fixed succ-degree orientation to
lower-threshold succ-degree root counts. -/
theorem succDegreeRootCountTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_orientation horient

/-- Challenge-facing bridge from the succ-degree positive-combination
hypotheses to Chudnovsky--Seymour compatibility. -/
theorem succDegreeCompatiblePair_of_posCombo
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) :
    Compatible f g :=
  Compatible.of_posComboRealRooted_succDegree hfg hf_pos hg_pos hdeg hf_split

/-- Challenge-facing derivative compatibility bridge for the succ-degree
positive-combination hypotheses. -/
theorem succDegreeDerivativeCompatiblePair_of_posCombo
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) :
    Compatible f.derivative g.derivative :=
  (succDegreeCompatiblePair_of_posCombo hf_pos hg_pos hfg hdeg hf_split).derivative

/-- Challenge-facing reduction from the compatible succ-degree root-count leaf
to the positive-combination leaf. -/
theorem succDegreeRootCountAboveNonRootTarget_of_compatible
    (hcount : compatibleSuccDegreeRootCountAboveNonRootTarget) :
    succDegreeRootCountAboveNonRootTarget :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible hcount

/-- Challenge-facing reduction from the compatible gap-at-most-two theorem and
the exact gap-two obstruction to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_leTwo_of_noGapTwo
    (hle2 : compatibleSuccDegreeRootCountAboveLeTwoTarget)
    (hgap : compatibleSuccDegreeRootCountAboveNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo hle2 hgap

/-- Challenge-facing derivative-induction bridge from the compatible
root-count target to the gap-at-most-two target.  The low-degree compatible
bases close the degree-zero and degree-one cases. -/
theorem compatibleSuccDegreeRootCountAboveLeTwoTarget_of_nonRoot
    (hcount : compatibleSuccDegreeRootCountAboveNonRootTarget) :
    compatibleSuccDegreeRootCountAboveLeTwoTarget :=
  compatibleSuccDegreeRootCountAboveLeTwo_of_nonRoot hcount

/-- Challenge-facing strong-induction bridge: the exact gap-two obstruction
alone closes the compatible common-non-root root-count target. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_noGapTwo
    (hgap : compatibleSuccDegreeRootCountAboveNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo hgap

/-- Challenge-facing direct reduction from the closed-segment exact gap-two
obstruction to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_closedSegment
    (hclosed : compatibleSuccDegreeClosedSegmentNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegment hclosed

/-- Challenge-facing direct reduction from closed-segment endpoint count
equality to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_closedSegmentCountEq
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hcount

/-- Challenge-facing reduction from closed-segment endpoint count equality to
the succ-degree common-non-root upper root-count leaf. -/
theorem succDegreeRootCountAboveNonRootTarget_of_closedSegmentCountEq
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    succDegreeRootCountAboveNonRootTarget :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hcount

/-- Challenge-facing reverse reduction from the compatible root-count leaf to
closed-segment endpoint count equality. -/
theorem compatibleSuccDegreeClosedSegmentCountEqTarget_of_nonRoot
    (hcount : compatibleSuccDegreeRootCountAboveNonRootTarget) :
    compatibleSuccDegreeClosedSegmentCountEqTarget :=
  compatibleSuccDegreeClosedSegmentCountEq_of_nonRoot hcount

/-- Challenge-facing equivalence between the closed-segment endpoint
count-equality target and the compatible common-non-root root-count leaf. -/
theorem compatibleSuccDegreeClosedSegmentCountEqTarget_iff_nonRootTarget :
    compatibleSuccDegreeClosedSegmentCountEqTarget ↔
      compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeClosedSegmentCountEq_iff_nonRoot

/-- Challenge-facing direct reduction from the right-pencil exact gap-two
obstruction to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_rightFamily
    (hright : compatibleSuccDegreeRightFamilyNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_rightFamily hright

/-- Challenge-facing direct reduction from the endpoint-sign exact gap-two
obstruction to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_endpointSign
    (hsign : compatibleSuccDegreeEndpointSignNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSign hsign

/-- Challenge-facing direct reduction from the lower-threshold endpoint-sign
exact gap obstruction to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_endpointSignLower
    (hlower : compatibleSuccDegreeEndpointSignLowerNoGapTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_endpointSignLower hlower

/-- Challenge-facing direct reduction from the exact lower-threshold
endpoint-sign count comparison to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_lowerCountEq
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_lowerCountEq hcount

/-- Challenge-facing reduction from the closed-segment exact gap-two
obstruction to the compatible exact gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoTarget_of_closedSegment
    (hclosed : compatibleSuccDegreeClosedSegmentNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNoGapTwoTarget :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment hclosed

/-- Challenge-facing reduction from closed-segment endpoint count equality to
the closed-segment exact gap-two obstruction. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwoTarget_of_countEq
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    compatibleSuccDegreeClosedSegmentNoGapTwoTarget :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_countEq hcount

/-- Challenge-facing reduction from closed-segment endpoint count equality to
the exact lower-threshold endpoint-sign count comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_closedSegmentCountEq
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_closedSegmentCountEq hcount

/-- Challenge-facing reduction from the exact lower-threshold endpoint-sign
count comparison to closed-segment endpoint count equality. -/
theorem compatibleSuccDegreeClosedSegmentCountEqTarget_of_lowerCountEq
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeClosedSegmentCountEqTarget :=
  compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hcount

/-- Challenge-facing equivalence between the closed-segment endpoint
count-equality target and the exact lower-threshold endpoint-sign count target. -/
theorem compatibleSuccDegreeClosedSegmentCountEqTarget_iff_lowerCountEqTarget :
    compatibleSuccDegreeClosedSegmentCountEqTarget ↔
      compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeClosedSegmentCountEq_iff_lowerCountEq

/-- Challenge-facing low-degree base case for closed-segment endpoint count
equality. -/
theorem compatibleSuccDegreeClosedSegmentCountEqPair_of_natDegree_le_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card :=
  compatibleSuccDegreeClosedSegmentCountEq_of_natDegree_le_one
    hcomp hf_pos hg_pos hdeg hf_split hfdeg hxf hxg hseg

/-- Challenge-facing degree-`≤ 1` base case for the #42 exact lower-threshold
endpoint-sign count comparison.  This is the degree-`≤ 1` base wrapper for the
lower-count endpoint-sign route: positivity of the endpoint product at the fixed
threshold rules out any closed-segment crossing, giving the exact lower-count
difference `= 1` directly, without a separate closed-segment no-crossing
hypothesis. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqPair_of_natDegree_le_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hprod : 0 < f.eval x * g.eval x) :
    ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1 :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_natDegree_le_one
    hcomp hf_pos hg_pos hdeg hf_split hfdeg hxf hxg hprod

/-- Challenge-facing low-degree base case for the exact gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoPair_of_natDegree_le_one
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 1)
    (x : ℝ) (_hxf : ¬ f.IsRoot x) (_hxg : ¬ g.IsRoot x) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_one
    hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing degree-two lower-threshold root-count base, reduced to
the quadratic/cubic root-order leaf. -/
theorem succDegreeRootCountPair_of_natDegree_eq_two_of_rootBounds
    (hbound : succDegreeQuadraticCubicRootBoundsTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 2) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_posCombo_natDegree_eq_two_of_rootBounds
    hbound hf_pos hg_pos hfg hdeg hf_split hfdeg x

/-- Challenge-facing degree-two upper-threshold root-count base, reduced to
the quadratic/cubic root-order leaf. -/
theorem succDegreeRootCountAbovePair_of_natDegree_eq_two_of_rootBounds
    (hbound : succDegreeQuadraticCubicRootBoundsTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 2) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_posCombo_natDegree_eq_two_of_rootBounds
    hbound hf_pos hg_pos hfg hdeg hf_split hfdeg x

/-- Challenge-facing degree-two exact no-gap base, reduced to the
quadratic/cubic root-order leaf. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoPair_of_natDegree_eq_two_of_rootBounds
    (hbound : succDegreeQuadraticCubicRootBoundsTarget)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree = 2)
    (x : ℝ) (_hxf : ¬ f.IsRoot x) (_hxg : ¬ g.IsRoot x) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_eq_two_of_rootBounds
    hbound hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing exact no-gap base through lower endpoint degree two,
reduced to the quadratic/cubic root-order leaf. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoPair_of_natDegree_le_two_of_rootBounds
    (hbound : succDegreeQuadraticCubicRootBoundsTarget)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2)
    (x : ℝ) (_hxf : ¬ f.IsRoot x) (_hxg : ¬ g.IsRoot x) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_rootBounds
    hbound hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing exact no-gap base through lower endpoint degree two,
reduced to the three quadratic/cubic obstruction leaves. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoPair_of_natDegree_le_two_of_obstructions
    (hfirst : succDegreeQuadraticCubicFirstAboveObstructionTarget)
    (hsecond : succDegreeQuadraticCubicSecondAboveObstructionTarget)
    (hbelow : succDegreeQuadraticCubicFullBelowObstructionTarget)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2)
    (x : ℝ) (_hxf : ¬ f.IsRoot x) (_hxg : ¬ g.IsRoot x) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_obstructions
    hfirst hsecond hbelow hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing exact no-gap base through lower endpoint degree two,
reduced to the three pure monic-pencil obstruction leaves. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoPair_of_natDegree_le_two_of_pencil_obstructions
    (hfirst : quadraticCubicFirstAbovePencilObstructionTarget)
    (hsecond : quadraticCubicSecondAbovePencilObstructionTarget)
    (hbelow : quadraticCubicFullBelowPencilObstructionTarget)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : f.natDegree ≤ 2)
    (x : ℝ) (_hxf : ¬ f.IsRoot x) (_hxg : ¬ g.IsRoot x) :
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≠ 2 :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_natDegree_le_two_of_pencil_obstructions
    hfirst hsecond hbelow hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing reduction from closed-segment endpoint count equality to
the compatible exact gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoTarget_of_closedSegmentCountEq
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    compatibleSuccDegreeRootCountAboveNoGapTwoTarget :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegmentCountEq hcount

/-- Challenge-facing reduction from the right-pencil exact gap-two obstruction
to the closed-segment exact gap-two obstruction. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwoTarget_of_rightFamily
    (hright : compatibleSuccDegreeRightFamilyNoGapTwoTarget) :
    compatibleSuccDegreeClosedSegmentNoGapTwoTarget :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_rightFamily hright

/-- Challenge-facing reduction from the right-pencil exact gap-two obstruction
to the endpoint-sign exact gap-two obstruction. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwoTarget_of_rightFamily
    (hright : compatibleSuccDegreeRightFamilyNoGapTwoTarget) :
    compatibleSuccDegreeEndpointSignNoGapTwoTarget :=
  compatibleSuccDegreeEndpointSignNoGapTwo_of_rightFamily hright

/-- Challenge-facing equivalence between the right-pencil and endpoint-sign
exact gap-two obstruction targets. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwoTarget_iff_endpointSignTarget :
    compatibleSuccDegreeRightFamilyNoGapTwoTarget ↔
      compatibleSuccDegreeEndpointSignNoGapTwoTarget :=
  compatibleSuccDegreeRightFamilyNoGapTwo_iff_endpointSign

/-- Challenge-facing reduction from the right-pencil exact gap-two obstruction
to the compatible exact gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoTarget_of_rightFamily
    (hright : compatibleSuccDegreeRightFamilyNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNoGapTwoTarget :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily hright

/-- Challenge-facing reduction from the endpoint-sign exact gap-two obstruction
to the right-pencil exact gap-two obstruction. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwoTarget_of_endpointSign
    (hsign : compatibleSuccDegreeEndpointSignNoGapTwoTarget) :
    compatibleSuccDegreeRightFamilyNoGapTwoTarget :=
  compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign hsign

/-- Challenge-facing reduction from the endpoint-sign exact gap-two obstruction
to the closed-segment exact gap-two obstruction. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwoTarget_of_endpointSign
    (hsign : compatibleSuccDegreeEndpointSignNoGapTwoTarget) :
    compatibleSuccDegreeClosedSegmentNoGapTwoTarget :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign hsign

/-- Challenge-facing reduction from the closed-segment exact gap-two obstruction
to the endpoint-sign exact gap-two obstruction. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwoTarget_of_closedSegment
    (hclosed : compatibleSuccDegreeClosedSegmentNoGapTwoTarget) :
    compatibleSuccDegreeEndpointSignNoGapTwoTarget :=
  compatibleSuccDegreeEndpointSignNoGapTwo_of_closedSegment hclosed

/-- Challenge-facing equivalence between the closed-segment and endpoint-sign
exact gap-two obstruction targets. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwoTarget_iff_endpointSignTarget :
    compatibleSuccDegreeClosedSegmentNoGapTwoTarget ↔
      compatibleSuccDegreeEndpointSignNoGapTwoTarget :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_iff_endpointSign

/-- Challenge-facing reduction from the endpoint-sign exact gap-two obstruction
to the compatible exact gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoTarget_of_endpointSign
    (hsign : compatibleSuccDegreeEndpointSignNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNoGapTwoTarget :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign hsign

/-- Challenge-facing reduction from the no-common orientation core to the
compatible succ-degree orientation target. -/
theorem compatibleSuccDegreePrecTarget_of_noCommonOrientation
    (hstep : noCommonOrientationTarget) :
    compatibleSuccDegreePrecTarget :=
  compatibleSuccDegreePrec_of_noCommonOrientation hstep

/-- Challenge-facing reduction from the all-combinations bridge to the
compatible succ-degree all-combinations target. -/
theorem compatibleSuccDegreeAllComboTarget_of_allComboBridge
    (hall : allComboBridgeTarget) :
    compatibleSuccDegreeAllComboTarget :=
  compatibleSuccDegreeAllCombo_of_allComboBridge hall

/-- Challenge-facing projection from the compatible succ-degree
all-combinations target to the negative right-pencil family. -/
theorem compatibleSuccDegreeNegativeRightFamilyTarget_of_allCombo
    (hall : compatibleSuccDegreeAllComboTarget) :
    compatibleSuccDegreeNegativeRightFamilyTarget :=
  compatibleSuccDegreeNegativeRightFamily_of_allCombo hall

/-- Challenge-facing projection from the compatible succ-degree
all-combinations target to the nonnegative-coefficient negative right-pencil
family. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonnegTarget_of_allCombo
    (hall : compatibleSuccDegreeAllComboTarget) :
    compatibleSuccDegreeNegativeRightFamilyNonnegTarget :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_allCombo hall

/-- Challenge-facing degree-zero base case for the nonnegative-coefficient
negative right-pencil family. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonnegTarget_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits)
    (hfdeg : f.natDegree = 0)
    (μ : ℝ) (hμ : μ < 0) :
    (f + C μ * g).Splits :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_natDegree_eq_zero
    hcomp hf_pos hg_pos hfnn hgnn hdeg hf_split hfdeg μ hμ

/-- Challenge-facing reduction from the all-combinations bridge to the
nonnegative-coefficient negative right-pencil family. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonnegTarget_of_allComboBridge
    (hall : allComboBridgeTarget) :
    compatibleSuccDegreeNegativeRightFamilyNonnegTarget :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_allComboBridge hall

/-- Challenge-facing reduction from the honest same-degree/succ-degree
orientation split to the nonnegative-coefficient negative right-pencil family.
-/
theorem compatibleSuccDegreeNegativeRightFamilyNonnegTarget_of_degreeSplit
    (hsame : sameDegreeOrientationAlternativeTarget)
    (hsucc : succDegreeOrientationTarget) :
    compatibleSuccDegreeNegativeRightFamilyNonnegTarget :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_degreeSplit hsame hsucc

/-- Challenge-facing reduction from the affine-family bridge to the
nonnegative-coefficient negative right-pencil family. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonnegTarget_of_affineFamily
    (haff : affineFamilyTarget) :
    compatibleSuccDegreeNegativeRightFamilyNonnegTarget :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_affineFamilyBridge haff

/-- Challenge-facing reduction from the boundary-right-pair orientation target
to the nonnegative-coefficient negative right-pencil family. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonnegTarget_of_boundaryRightPairOrientation
    (hboundary : boundaryRightPairOrientationTarget) :
    compatibleSuccDegreeNegativeRightFamilyNonnegTarget :=
  compatibleSuccDegreeNegativeRightFamilyNonneg_of_boundaryRightPairOrientation hboundary

/-- Challenge-facing projection from the compatible succ-degree all-combinations
target to the signed right-pencil family. -/
theorem compatibleSuccDegreeSignedRightFamilyTarget_of_allCombo
    (hall : compatibleSuccDegreeAllComboTarget) :
    compatibleSuccDegreeSignedRightFamilyTarget :=
  compatibleSuccDegreeSignedRightFamily_of_allCombo hall

/-- Challenge-facing reduction from the signed right-pencil family to the
compatible succ-degree all-combinations target. -/
theorem compatibleSuccDegreeAllComboTarget_of_signedRightFamily
    (hsigned : compatibleSuccDegreeSignedRightFamilyTarget) :
    compatibleSuccDegreeAllComboTarget :=
  compatibleSuccDegreeAllCombo_of_signedRightFamily hsigned

/-- Challenge-facing reduction from the negative right-pencil family to the
signed right-pencil family. -/
theorem compatibleSuccDegreeSignedRightFamilyTarget_of_negativeRightFamily
    (hneg : compatibleSuccDegreeNegativeRightFamilyTarget) :
    compatibleSuccDegreeSignedRightFamilyTarget :=
  compatibleSuccDegreeSignedRightFamily_of_negativeRightFamily hneg

/-- Challenge-facing reduction from the nonnegative-coefficient negative
right-pencil family to the coefficient-free negative right-pencil family. -/
theorem compatibleSuccDegreeNegativeRightFamilyTarget_of_nonnegShift
    (hneg : compatibleSuccDegreeNegativeRightFamilyNonnegTarget) :
    compatibleSuccDegreeNegativeRightFamilyTarget :=
  compatibleSuccDegreeNegativeRightFamily_of_nonnegShift hneg

/-- Challenge-facing reduction from the negative right-pencil family to the
compatible succ-degree all-combinations target. -/
theorem compatibleSuccDegreeAllComboTarget_of_negativeRightFamily
    (hneg : compatibleSuccDegreeNegativeRightFamilyTarget) :
    compatibleSuccDegreeAllComboTarget :=
  compatibleSuccDegreeAllCombo_of_negativeRightFamily hneg

/-- Challenge-facing reduction from the nonnegative-coefficient negative
right-pencil family to the compatible succ-degree all-combinations target. -/
theorem compatibleSuccDegreeAllComboTarget_of_negativeRightFamily_nonnegShift
    (hneg : compatibleSuccDegreeNegativeRightFamilyNonnegTarget) :
    compatibleSuccDegreeAllComboTarget :=
  compatibleSuccDegreeAllCombo_of_negativeRightFamily_nonnegShift hneg

/-- Challenge-facing reduction from the compatible succ-degree all-combinations
target to the compatible succ-degree orientation target. -/
theorem compatibleSuccDegreePrecTarget_of_allCombo
    (hall : compatibleSuccDegreeAllComboTarget) :
    compatibleSuccDegreePrecTarget :=
  compatibleSuccDegreePrec_of_allCombo hall

/-- Challenge-facing reduction from the signed right-pencil family to the
compatible succ-degree orientation target. -/
theorem compatibleSuccDegreePrecTarget_of_signedRightFamily
    (hsigned : compatibleSuccDegreeSignedRightFamilyTarget) :
    compatibleSuccDegreePrecTarget :=
  compatibleSuccDegreePrec_of_signedRightFamily hsigned

/-- Challenge-facing reduction from the negative right-pencil family to the
compatible succ-degree orientation target. -/
theorem compatibleSuccDegreePrecTarget_of_negativeRightFamily
    (hneg : compatibleSuccDegreeNegativeRightFamilyTarget) :
    compatibleSuccDegreePrecTarget :=
  compatibleSuccDegreePrec_of_negativeRightFamily hneg

/-- Challenge-facing reduction from the nonnegative-coefficient negative
right-pencil family to the compatible succ-degree orientation target. -/
theorem compatibleSuccDegreePrecTarget_of_negativeRightFamily_nonnegShift
    (hneg : compatibleSuccDegreeNegativeRightFamilyNonnegTarget) :
    compatibleSuccDegreePrecTarget :=
  compatibleSuccDegreePrec_of_negativeRightFamily_nonnegShift hneg

/-- Challenge-facing reduction from the all-combinations bridge to the
compatible succ-degree orientation target. -/
theorem compatibleSuccDegreePrecTarget_of_allComboBridge
    (hall : allComboBridgeTarget) :
    compatibleSuccDegreePrecTarget :=
  compatibleSuccDegreePrec_of_allComboBridge hall

/-- Challenge-facing reduction from the compatible succ-degree orientation
target to the exact lower-threshold endpoint-sign count comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_prec
    (hprec : compatibleSuccDegreePrecTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_prec hprec

/-- Challenge-facing reduction from the compatible succ-degree all-combinations
target to the exact lower-threshold endpoint-sign count comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_allCombo
    (hall : compatibleSuccDegreeAllComboTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo hall

/-- Challenge-facing reduction from the signed right-pencil family to the exact
lower-threshold endpoint-sign count comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_signedRightFamily
    (hsigned : compatibleSuccDegreeSignedRightFamilyTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_signedRightFamily hsigned

/-- Challenge-facing reduction from the negative right-pencil family to the
exact lower-threshold endpoint-sign count comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_negativeRightFamily
    (hneg : compatibleSuccDegreeNegativeRightFamilyTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily hneg

/-- Challenge-facing reduction from the nonnegative-coefficient negative
right-pencil family to the exact lower-threshold endpoint-sign count
comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_negativeRightFamily_nonnegShift
    (hneg : compatibleSuccDegreeNegativeRightFamilyNonnegTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily_nonnegShift hneg

/-- Challenge-facing reduction from the no-common orientation core to the exact
lower-threshold endpoint-sign count comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_noCommonOrientation
    (hstep : noCommonOrientationTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_prec
    (compatibleSuccDegreePrec_of_noCommonOrientation hstep)

/-- Challenge-facing reduction from the all-combinations bridge to the exact
lower-threshold endpoint-sign count comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEqTarget_of_allComboBridge
    (hall : allComboBridgeTarget) :
    compatibleSuccDegreeEndpointSignLowerCountEqTarget :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_allComboBridge hall

/-- Challenge-facing reduction from the exact lower-threshold endpoint-sign
count comparison to the lower-threshold endpoint-sign exact gap obstruction. -/
theorem compatibleSuccDegreeEndpointSignLowerNoGapTarget_of_lowerCountEq
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeEndpointSignLowerNoGapTarget :=
  compatibleSuccDegreeEndpointSignLowerNoGap_of_lowerCountEq hcount

/-- Challenge-facing reduction from the lower-threshold endpoint-sign exact gap
obstruction to the endpoint-sign exact gap-two obstruction. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwoTarget_of_lower
    (hlower : compatibleSuccDegreeEndpointSignLowerNoGapTarget) :
    compatibleSuccDegreeEndpointSignNoGapTwoTarget :=
  compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower

/-- Challenge-facing reduction from the exact lower-threshold endpoint-sign
count comparison to the endpoint-sign exact gap-two obstruction. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwoTarget_of_lowerCountEq
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeEndpointSignNoGapTwoTarget :=
  compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount

/-- Challenge-facing reduction from the lower-threshold endpoint-sign exact gap
obstruction to the right-pencil exact gap-two obstruction. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwoTarget_of_endpointSignLower
    (hlower : compatibleSuccDegreeEndpointSignLowerNoGapTarget) :
    compatibleSuccDegreeRightFamilyNoGapTwoTarget :=
  compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSignLower hlower

/-- Challenge-facing reduction from the exact lower-threshold endpoint-sign
count comparison to the right-pencil exact gap-two obstruction. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwoTarget_of_lowerCountEq
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeRightFamilyNoGapTwoTarget :=
  compatibleSuccDegreeRightFamilyNoGapTwo_of_lowerCountEq hcount

/-- Challenge-facing reduction from the lower-threshold endpoint-sign exact gap
obstruction to the closed-segment exact gap-two obstruction. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwoTarget_of_endpointSignLower
    (hlower : compatibleSuccDegreeEndpointSignLowerNoGapTarget) :
    compatibleSuccDegreeClosedSegmentNoGapTwoTarget :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSignLower hlower

/-- Challenge-facing reduction from the exact lower-threshold endpoint-sign
count comparison to the closed-segment exact gap-two obstruction. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwoTarget_of_lowerCountEq
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeClosedSegmentNoGapTwoTarget :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_lowerCountEq hcount

/-- Challenge-facing reduction from the lower-threshold endpoint-sign exact gap
obstruction to the compatible exact gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoTarget_of_endpointSignLower
    (hlower : compatibleSuccDegreeEndpointSignLowerNoGapTarget) :
    compatibleSuccDegreeRootCountAboveNoGapTwoTarget :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSignLower hlower

/-- Challenge-facing reduction from the exact lower-threshold endpoint-sign
count comparison to the compatible exact gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwoTarget_of_lowerCountEq
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeRootCountAboveNoGapTwoTarget :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_lowerCountEq hcount

/-- Challenge-facing reduction from the compatible gap-at-most-two theorem and
the closed-segment exact gap-two obstruction to the compatible root-count
leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_leTwo_of_closedSegment
    (hle2 : compatibleSuccDegreeRootCountAboveLeTwoTarget)
    (hclosed : compatibleSuccDegreeClosedSegmentNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_closedSegment hle2 hclosed

/-- Challenge-facing reduction from the compatible gap-at-most-two theorem and
the right-pencil exact gap-two obstruction to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_leTwo_of_rightFamily
    (hle2 : compatibleSuccDegreeRootCountAboveLeTwoTarget)
    (hright : compatibleSuccDegreeRightFamilyNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_rightFamily hle2 hright

/-- Challenge-facing reduction from the compatible gap-at-most-two theorem and
the endpoint-sign exact gap-two obstruction to the compatible root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_leTwo_of_endpointSign
    (hle2 : compatibleSuccDegreeRootCountAboveLeTwoTarget)
    (hsign : compatibleSuccDegreeEndpointSignNoGapTwoTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSign hle2 hsign

/-- Challenge-facing reduction from the compatible gap-at-most-two theorem and
the lower-threshold endpoint-sign exact gap obstruction to the compatible
root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_leTwo_of_endpointSignLower
    (hle2 : compatibleSuccDegreeRootCountAboveLeTwoTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerNoGapTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSignLower hle2 hlower

/-- Challenge-facing reduction from the compatible gap-at-most-two theorem and
the exact lower-threshold endpoint-sign count comparison to the compatible
root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootTarget_of_leTwo_of_lowerCountEq
    (hle2 : compatibleSuccDegreeRootCountAboveLeTwoTarget)
    (hcount : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    compatibleSuccDegreeRootCountAboveNonRootTarget :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_lowerCountEq hle2 hcount

/-- Challenge-facing closed-segment real-rootedness package for positive
segment parameters in a compatible succ-degree pair. -/
theorem compatibleSuccDegreeClosedSegmentRealRooted_of_pos
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g) ≠ 0 ∧
      (C (1 - β) * f + C β * g).Splits :=
  compatibleSuccDegree_closedSegment_isRealRooted_of_pos
    hcomp hg_pos hdeg hβ0 hβ1

/-- Challenge-facing degree package for positive closed-segment parameters in
a compatible succ-degree pair. -/
theorem compatibleSuccDegreeClosedSegmentNatDegreeEqRight_of_pos
    {f g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) :
    (C (1 - β) * f + C β * g).natDegree = g.natDegree :=
  succDegree_closedSegment_natDegree_eq_right_of_pos hg_pos hdeg hβ0

/-- Challenge-facing root-cardinality package for positive closed-segment
parameters in a compatible succ-degree pair. -/
theorem compatibleSuccDegreeClosedSegmentRootsCardEqSucc_of_pos
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g).roots.card = f.natDegree + 1 :=
  compatibleSuccDegree_closedSegment_roots_card_eq_succ_of_pos
    hcomp hg_pos hdeg hβ0 hβ1

/-- Challenge-facing derivative application of the compatible succ-degree
root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRootDerivativePair
    (hcount : compatibleSuccDegreeRootCountAboveNonRootTarget)
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree) (x : ℝ)
    (hxf : ¬ f.derivative.IsRoot x) (hxg : ¬ g.derivative.IsRoot x) :
    ((f.derivative.roots.filter (x < ·)).card : ℤ) -
        (g.derivative.roots.filter (x < ·)).card ≤ 1 ∧
    ((g.derivative.roots.filter (x < ·)).card : ℤ) -
        (f.derivative.roots.filter (x < ·)).card ≤ 1 :=
  compatibleSuccDegreeRootCountAboveNonRoot_derivative
    hcount hcomp hf_pos hg_pos hdeg hf_split hfdeg x hxf hxg

/-- Challenge-facing derivative application of the compatible succ-degree
root-count leaf, promoted to all thresholds. -/
theorem compatibleSuccDegreeRootCountAboveDerivativePair
    (hcount : compatibleSuccDegreeRootCountAboveNonRootTarget)
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree) (x : ℝ) :
    ((f.derivative.roots.filter (x < ·)).card : ℤ) -
        (g.derivative.roots.filter (x < ·)).card ≤ 1 ∧
    ((g.derivative.roots.filter (x < ·)).card : ℤ) -
        (f.derivative.roots.filter (x < ·)).card ≤ 1 :=
  compatibleSuccDegreeRootCountAbove_derivative
    hcount hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing `Prec`-to-root-count bridge in upper-threshold form. -/
theorem succDegreeRootCountAbovePair_of_prec
    {f g : ℝ[X]} (hprec : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) (x : ℝ) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
    ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_prec hprec hdeg x

/-- Challenge-facing oriented `Prec`-to-root-count bridge in upper-threshold
form. -/
theorem succDegreeRootCountAboveOrientedPair_of_prec
    {f g : ℝ[X]} (hprec : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) (x : ℝ) :
    ((f.roots.filter (x < ·)).card : ℤ) ≤ (g.roots.filter (x < ·)).card ∧
    ((g.roots.filter (x < ·)).card : ℤ) ≤
      (f.roots.filter (x < ·)).card + 1 :=
  succDegreeRootCountAboveOriented_of_prec hprec hdeg x

/-- Challenge-facing `Prec`-to-root-count bridge in lower-threshold form. -/
theorem succDegreeRootCountPair_of_prec
    {f g : ℝ[X]} (hprec : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
    ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_prec hprec hdeg x

/-- Challenge-facing Rolle root-count bridge in upper-threshold form. -/
theorem rootCountAboveDerivativePair_of_splits
    {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) (x : ℝ) :
    ((p.derivative.roots.filter (x < ·)).card : ℤ) -
        (p.roots.filter (x < ·)).card ≤ 1 ∧
    ((p.roots.filter (x < ·)).card : ℤ) -
        (p.derivative.roots.filter (x < ·)).card ≤ 1 :=
  rootCountAbove_derivative_diff_le_one_of_splits hp hdeg x

/-- Challenge-facing oriented Rolle root-count bridge in upper-threshold
form. -/
theorem rootCountAboveDerivativeOrientedPair_of_splits
    {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) (x : ℝ) :
    ((p.derivative.roots.filter (x < ·)).card : ℤ) ≤
        (p.roots.filter (x < ·)).card ∧
    ((p.roots.filter (x < ·)).card : ℤ) ≤
        (p.derivative.roots.filter (x < ·)).card + 1 :=
  rootCountAbove_derivative_oriented_of_splits hp hdeg x

/-- Challenge-facing forward derivative gap propagation for upper root
counts. -/
theorem rootCountAboveDerivativeSubGeTwo_of_subGeThree
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree) {x : ℝ}
    (hgap : 3 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
      (g.roots.filter (x < ·)).card) :
    2 ≤ ((f.derivative.roots.filter (x < ·)).card : ℤ) -
      (g.derivative.roots.filter (x < ·)).card :=
  rootCountAbove_derivative_sub_ge_two_of_sub_ge_three hf hg hfdeg hgdeg hgap

/-- Challenge-facing reverse derivative gap propagation for upper root
counts. -/
theorem rootCountAboveDerivativeRevSubGeTwo_of_subGeThree
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree) {x : ℝ}
    (hgap : 3 ≤ ((g.roots.filter (x < ·)).card : ℤ) -
      (f.roots.filter (x < ·)).card) :
    2 ≤ ((g.derivative.roots.filter (x < ·)).card : ℤ) -
      (f.derivative.roots.filter (x < ·)).card :=
  rootCountAbove_derivative_rev_sub_ge_two_of_sub_ge_three hf hg hfdeg hgdeg hgap

/-- Challenge-facing bridge: derivative induction rules out upper-count gaps
of size at least three for compatible succ-degree pairs. -/
theorem compatibleSuccDegreeRootCountAboveLeTwoPair_of_derivative
    (hcount : compatibleSuccDegreeRootCountAboveNonRootTarget)
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree) (x : ℝ) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 2 ∧
    ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 2 :=
  compatibleSuccDegreeRootCountAbove_le_two_of_derivative
    hcount hcomp hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing positive-combination specialization of the gap-at-most-two
derivative-induction bridge. -/
theorem succDegreeRootCountAboveLeTwoPair_of_derivative
    (hcount : compatibleSuccDegreeRootCountAboveNonRootTarget)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree) (x : ℝ) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 2 ∧
    ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 2 :=
  compatibleSuccDegreeRootCountAboveLeTwoPair_of_derivative hcount
    (succDegreeCompatiblePair_of_posCombo hf_pos hg_pos hfg hdeg hf_split)
    hf_pos hg_pos hdeg hf_split hfdeg x

/-- Challenge-facing Rolle root-count bridge in lower-threshold form. -/
theorem rootCountDerivativePair_of_splits
    {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) (x : ℝ) :
    ((p.derivative.roots.filter (· ≤ x)).card : ℤ) -
        (p.roots.filter (· ≤ x)).card ≤ 0 ∧
    ((p.roots.filter (· ≤ x)).card : ℤ) -
        (p.derivative.roots.filter (· ≤ x)).card ≤ 2 :=
  rootCount_derivative_diff_le_two_of_splits hp hdeg x

/-- Challenge-facing reduction from succ-degree root counts to succ-degree
root crossing. -/
theorem succDegreeRootCrossingTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCount hcount

/-- Challenge-facing reduction from upper-threshold succ-degree root counts to
succ-degree root crossing. -/
theorem succDegreeRootCrossingTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hcount

/-- Challenge-facing conversion from upper-threshold succ-degree root counts
to lower-threshold succ-degree root counts. -/
theorem succDegreeRootCountTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_rootCountAbove hcount

/-- Challenge-facing conversion from lower-threshold succ-degree root counts
to upper-threshold succ-degree root counts. -/
theorem succDegreeRootCountAboveTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_rootCount hcount

/-- Challenge-facing equivalence between the lower- and upper-threshold
succ-degree root-count formulations. -/
theorem succDegreeRootCountAboveTarget_iff_rootCount :
    succDegreeRootCountAboveTarget ↔ succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_iff_rootCount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the full upper-threshold formulation. -/
theorem succDegreeRootCountAboveTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot hcount

/-- Challenge-facing equivalence between the upper and lower common-non-root
succ-degree root-count formulations. -/
theorem succDegreeRootCountAboveNonRootTarget_iff_rootCountNonRoot :
    succDegreeRootCountAboveNonRootTarget ↔ succDegreeRootCountNonRootTarget :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_iff_rootCountNonRoot

/-- Challenge-facing reduction from the common-left-interleaver formulation to
the lower common-non-root succ-degree root-count leaf. -/
theorem succDegreeRootCountNonRootTarget_of_commonLeftInterleaver
    (hleft : succDegreeCommonLeftInterleaverTarget) :
    succDegreeRootCountNonRootTarget :=
  posComboNoCommonSuccDegreeRootCountNonRoot_of_commonLeftInterleaver hleft

/-- Challenge-facing reduction from the common-left-interleaver formulation to
the upper common-non-root succ-degree root-count leaf. -/
theorem succDegreeRootCountAboveNonRootTarget_of_commonLeftInterleaver
    (hleft : succDegreeCommonLeftInterleaverTarget) :
    succDegreeRootCountAboveNonRootTarget :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver hleft

/-- Challenge-facing reduction from the fixed succ-degree orientation to the
common-left-interleaver formulation. -/
theorem succDegreeCommonLeftInterleaverTarget_of_orientation
    (horient : succDegreeOrientationTarget) :
    succDegreeCommonLeftInterleaverTarget :=
  posComboNoCommonSuccDegreeCommonLeftInterleaver_of_orientation horient

/-- Challenge-facing reduction from common-non-root succ-degree lower root
counts to the full upper-threshold formulation. -/
theorem succDegreeRootCountAboveTarget_of_rootCountNonRoot
    (hcount : succDegreeRootCountNonRootTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the lower-threshold formulation. -/
theorem succDegreeRootCountTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_nonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the lower-threshold formulation, with an explicit name for the
`rootCountAboveNonRoot` leaf. -/
theorem succDegreeRootCountTarget_of_rootCountAboveNonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeRootCountTarget :=
  succDegreeRootCountTarget_of_nonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree lower root
counts to the full lower-threshold formulation. -/
theorem succDegreeRootCountTarget_of_rootCountNonRoot
    (hcount : succDegreeRootCountNonRootTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree lower root
counts to root crossing. -/
theorem succDegreeRootCrossingTarget_of_rootCountNonRoot
    (hcount : succDegreeRootCountNonRootTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to root crossing. -/
theorem succDegreeRootCrossingTarget_of_rootCountAboveNonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hcount

/-- Challenge-facing right-pencil parity bridge for succ-degree upper root
counts. -/
theorem succDegreeRootCountAbove_oddDiff_iff_pencilCrossing
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hf_split hxf hxg

/-- Challenge-facing endpoint-sign form of the succ-degree upper root-count
parity bridge. -/
theorem succDegreeRootCountAbove_oddDiff_iff_eval_mul_neg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔ f.eval x * g.eval x < 0) :=
  succDegree_odd_roots_gt_count_sub_iff_eval_mul_neg
    hf_pos hg_pos hfg hdeg hf_split hxf hxg

/-- Challenge-facing gap-two sign consequence for succ-degree upper root
counts. -/
theorem succDegreeRootCountAbove_eval_mul_pos_of_gapTwo
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    hf_pos hg_pos hfg hdeg hf_split hxf hxg hcount

/-- Challenge-facing reverse gap-two sign consequence for succ-degree upper
root counts. -/
theorem succDegreeRootCountAbove_eval_mul_pos_of_reverseGapTwo
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    hf_pos hg_pos hfg hdeg hf_split hxf hxg hcount

/-- Challenge-facing closed-segment nonvanishing consequence of a forward
upper root-count gap of two. -/
theorem succDegreeRootCountAbove_closedSegmentNotRoot_of_gapTwo
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  succDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    hf_pos hg_pos hfg hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Challenge-facing closed-segment nonvanishing consequence of a reverse
upper root-count gap of two. -/
theorem succDegreeRootCountAbove_closedSegmentNotRoot_of_reverseGapTwo
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  succDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    hf_pos hg_pos hfg hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Challenge-facing compatible endpoint-sign consequence for a forward
succ-degree upper root-count gap of two. -/
theorem compatibleSuccDegreeRootCountAbove_eval_mul_pos_of_gapTwo
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  compatibleSuccDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    hcomp hf_pos hg_pos hdeg hf_split hxf hxg hcount

/-- Challenge-facing compatible endpoint-sign consequence for a reverse
succ-degree upper root-count gap of two. -/
theorem compatibleSuccDegreeRootCountAbove_eval_mul_pos_of_reverseGapTwo
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  compatibleSuccDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    hcomp hf_pos hg_pos hdeg hf_split hxf hxg hcount

/-- Challenge-facing compatible closed-segment nonvanishing consequence of a
forward upper root-count gap of two. -/
theorem compatibleSuccDegreeRootCountAbove_closedSegmentNotRoot_of_gapTwo
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  compatibleSuccDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Challenge-facing compatible closed-segment nonvanishing consequence of a
reverse upper root-count gap of two. -/
theorem compatibleSuccDegreeRootCountAbove_closedSegmentNotRoot_of_reverseGapTwo
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  compatibleSuccDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Challenge-facing right-pencil parity bridge for succ-degree lower root
counts. -/
theorem succDegreeRootCount_evenDiff_iff_pencilCrossing
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :=
  succDegree_even_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hf_split hxf hxg

/-- Challenge-facing endpoint-sign form of the succ-degree lower root-count
parity bridge. -/
theorem succDegreeRootCount_evenDiff_iff_eval_mul_neg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔ f.eval x * g.eval x < 0) :=
  succDegree_even_roots_le_count_sub_iff_eval_mul_neg
    hf_pos hg_pos hfg hdeg hf_split hxf hxg

/-- Challenge-facing reduction from the succ-degree constant-term branches to
the full lower-threshold root-count formulation. -/
theorem succDegreeRootCountTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_residual_and_lead hlead hres

/-- Challenge-facing split of the succ-degree lead root-count branch by the
higher-degree constant term. -/
theorem succDegreeRootCountLeadTarget_of_bothNonzero_and_rightZero
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hright : succDegreeRootCountLeadRightZeroTarget) :
    succDegreeRootCountLeadTarget :=
  posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_rightZero
    hboth hright

/-- Challenge-facing `divX` reduction of the right-zero lead root-count branch. -/
theorem succDegreeRootCountLeadRightZeroTarget_of_divX_sameDegreeCount
    (hcount :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        f.coeff 0 ≠ 0 →
        g.coeff 0 = 0 →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) ≤
              (g.divX.roots.filter (· ≤ x)).card ∧
          ((g.divX.roots.filter (· ≤ x)).card : ℤ) ≤
              (f.roots.filter (· ≤ x)).card + 1) :
    succDegreeRootCountLeadRightZeroTarget :=
  posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCount
    hcount

/-- Challenge-facing upper-threshold `divX` reduction of the right-zero lead
root-count branch. -/
theorem succDegreeRootCountLeadRightZeroTarget_of_divX_sameDegreeCountAbove
    (hcount :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        f.coeff 0 ≠ 0 →
        g.coeff 0 = 0 →
        ∀ x : ℝ,
          ((g.divX.roots.filter (x < ·)).card : ℤ) ≤
              (f.roots.filter (x < ·)).card ∧
          ((f.roots.filter (x < ·)).card : ℤ) ≤
              (g.divX.roots.filter (x < ·)).card + 1) :
    succDegreeRootCountLeadRightZeroTarget :=
  posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_sameDegreeCountAbove
    hcount

/-- Challenge-facing `Prec`/`divX` reduction of the right-zero lead root-count
branch. -/
theorem succDegreeRootCountLeadRightZeroTarget_of_divX_prec
    (horient : succDegreeRootCountLeadRightZeroDivXPrecTarget) :
    succDegreeRootCountLeadRightZeroTarget :=
  posComboNoCommonSuccDegreeRootCountLeadRightZero_of_divX_prec
    horient

/-- Challenge-facing reduction from the sharper right-zero orientation target
to the `divX` orientation target. -/
theorem succDegreeRootCountLeadRightZeroDivXPrecTarget_of_prec
    (horient : succDegreeRootCountLeadRightZeroPrecTarget) :
    succDegreeRootCountLeadRightZeroDivXPrecTarget :=
  posComboNoCommonSuccDegreeRootCountLeadRightZeroDivXPrec_of_precFG
    horient

/-- Challenge-facing converse reduction: the sharper right-zero orientation
target `Prec f g` follows from the `divX` orientation target `Prec (g.divX) f`.
The degree-drop reconstruction is isolated in
`prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero`.

Together with `succDegreeRootCountLeadRightZeroDivXPrecTarget_of_prec` this shows
that on the right-zero lead branch the two orientation targets are equivalent. -/
theorem succDegreeRootCountLeadRightZeroPrecTarget_of_divXPrec
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget) :
    succDegreeRootCountLeadRightZeroPrecTarget :=
  posComboNoCommonSuccDegreeRootCountLeadRightZeroPrecFG_of_divX hdivX

/-- Challenge-facing equivalence between the sharper right-zero orientation
target and the `divX` orientation target. -/
theorem succDegreeRootCountLeadRightZeroPrecTarget_iff_divXPrecTarget :
    succDegreeRootCountLeadRightZeroPrecTarget ↔
      succDegreeRootCountLeadRightZeroDivXPrecTarget :=
  posComboNoCommonSuccDegreeRootCountLeadRightZeroPrecFG_iff_divXPrec

/-- Challenge-facing reduction from the sharper right-zero orientation target
to the right-zero lead root-count branch. -/
theorem succDegreeRootCountLeadRightZeroTarget_of_prec
    (horient : succDegreeRootCountLeadRightZeroPrecTarget) :
    succDegreeRootCountLeadRightZeroTarget :=
  succDegreeRootCountLeadRightZeroTarget_of_divX_prec
    (succDegreeRootCountLeadRightZeroDivXPrecTarget_of_prec horient)

/-- Challenge-facing reduction from the both-nonzero lead branch and the
right-zero `divX` orientation target to the full lead branch. -/
theorem succDegreeRootCountLeadTarget_of_bothNonzero_and_divXPrec
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget) :
    succDegreeRootCountLeadTarget :=
  posComboNoCommonSuccDegreeRootCountLead_of_bothNonzero_and_divX_prec
    hboth hdivX

/-- Challenge-facing reduction from the residual branch and the two lead
subbranches to the full lower-threshold root-count formulation. -/
theorem succDegreeRootCountTarget_of_residual_and_leadSubbranches
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hright : succDegreeRootCountLeadRightZeroTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCountTarget :=
  succDegreeRootCountTarget_of_residual_and_lead
    (succDegreeRootCountLeadTarget_of_bothNonzero_and_rightZero hboth hright)
    hres

/-- Challenge-facing reduction from the residual branch, the both-nonzero lead
branch, and the right-zero `divX` orientation target to the full lower-threshold
root-count formulation. -/
theorem succDegreeRootCountTarget_of_residual_bothNonzero_divXPrec
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_residual_bothNonzero_divX_prec
    hboth hdivX hres

/-- Challenge-facing reduction from the residual orientation target, the
both-nonzero lead branch, and the right-zero `divX` orientation target to the
full lower-threshold root-count formulation. -/
theorem succDegreeRootCountTarget_of_residualPrec_bothNonzero_divXPrec
    (hresPrec : succDegreeRootCountResidualPrecTarget)
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget) :
    succDegreeRootCountTarget :=
  posComboNoCommonSuccDegreeRootCount_of_residualPrec_bothNonzero_divX_prec
    hresPrec hboth hdivX

/-- Challenge-facing reduction from the succ-degree constant-term branches to
the upper-threshold root-count formulation. -/
theorem succDegreeRootCountAboveTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from the succ-degree constant-term branches to
root crossing. -/
theorem succDegreeRootCrossingTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from the residual branch, the both-nonzero lead
branch, and the right-zero `divX` orientation target to the upper-threshold
root-count formulation. -/
theorem succDegreeRootCountAboveTarget_of_residual_bothNonzero_divXPrec
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_residual_bothNonzero_divX_prec
    hboth hdivX hres

/-- Challenge-facing reduction from the residual orientation target, the
both-nonzero lead branch, and the right-zero `divX` orientation target to the
upper-threshold root-count formulation. -/
theorem succDegreeRootCountAboveTarget_of_residualPrec_bothNonzero_divXPrec
    (hresPrec : succDegreeRootCountResidualPrecTarget)
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget) :
    succDegreeRootCountAboveTarget :=
  posComboNoCommonSuccDegreeRootCountAbove_of_residualPrec_bothNonzero_divX_prec
    hresPrec hboth hdivX

/-- Challenge-facing reduction from the residual branch, the both-nonzero lead
branch, and the right-zero `divX` orientation target to succ-degree root
crossing. -/
theorem succDegreeRootCrossingTarget_of_residual_bothNonzero_divXPrec
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_residual_bothNonzero_divX_prec
    hboth hdivX hres

/-- Challenge-facing reduction from the residual orientation target, the
both-nonzero lead branch, and the right-zero `divX` orientation target to
succ-degree root crossing. -/
theorem succDegreeRootCrossingTarget_of_residualPrec_bothNonzero_divXPrec
    (hresPrec : succDegreeRootCountResidualPrecTarget)
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget) :
    succDegreeRootCrossingTarget :=
  posComboNoCommonSuccDegreeRootCrossing_of_residualPrec_bothNonzero_divX_prec
    hresPrec hboth hdivX

/-- Challenge-facing reduction from residual interlacing orientation to the
residual succ-degree root-count target. -/
theorem succDegreeRootCountResidualTarget_of_prec
    (hresPrec : succDegreeRootCountResidualPrecTarget) :
    succDegreeRootCountResidualTarget :=
  posComboNoCommonSuccDegreeRootCountResidual_of_prec hresPrec

/-- Challenge-facing reduction from the lead root-count branch and residual
interlacing orientation to the full lower-threshold root-count target. -/
theorem succDegreeRootCountTarget_of_lead_and_residualPrec
    (hlead : succDegreeRootCountLeadTarget)
    (hresPrec : succDegreeRootCountResidualPrecTarget) :
    succDegreeRootCountTarget :=
  succDegreeRootCountTarget_of_residual_and_lead hlead
    (succDegreeRootCountResidualTarget_of_prec hresPrec)

/-- Challenge-facing reduction from the lead root-count branch and residual
interlacing orientation to the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_lead_and_residualPrec
    (hlead : succDegreeRootCountLeadTarget)
    (hresPrec : succDegreeRootCountResidualPrecTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_residual_and_lead hlead
    (succDegreeRootCountResidualTarget_of_prec hresPrec)

/-- Challenge-facing reduction from succ-degree root counts to slot data. -/
theorem succDegreeSlotDataTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCount hcount

/-- Challenge-facing reduction from succ-degree upper-threshold root counts to
slot data. -/
theorem succDegreeSlotDataTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCountAbove hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to slot data. -/
theorem succDegreeSlotDataTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_nonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to slot data, with an explicit name for the `rootCountAboveNonRoot`
leaf. -/
theorem succDegreeSlotDataTarget_of_rootCountAboveNonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCountAboveNonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree lower root
counts to slot data. -/
theorem succDegreeSlotDataTarget_of_rootCountNonRoot
    (hcount : succDegreeRootCountNonRootTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from the succ-degree constant-term branches to
slot data. -/
theorem succDegreeSlotDataTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from succ-degree root counts to the repaired
succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_rootCount
    (hcount : succDegreeRootCountTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCount hcount

/-- Challenge-facing reduction from succ-degree upper-threshold root counts to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_rootCountAbove
    (hcount : succDegreeRootCountAboveTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_nonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_nonRoot hcount

/-- Challenge-facing reduction from common-non-root succ-degree upper root
counts to the repaired succ-degree pair endpoint, with an explicit name for the
`rootCountAboveNonRoot` leaf. -/
theorem succDegreePairTarget_of_rootCountAboveNonRoot
    (hcount : succDegreeRootCountAboveNonRootTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hcount

/-- Challenge-facing reduction from closed-segment endpoint count equality to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_closedSegmentCountEq
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq hcount

/-- Challenge-facing direct reduction from the #42 exact lower-threshold
endpoint-sign count equality leaf to the repaired succ-degree pair endpoint.
This is the single-hypothesis lower-count endpoint-sign route: it composes the
lower-count/closed-segment count bridge with
`succDegreePairTarget_of_closedSegmentCountEq`, so downstream users can discharge
the #42 succ-degree endpoint from the lower-count leaf alone. -/
theorem succDegreePairTarget_of_lowerCountEq
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    succDegreePairTarget :=
  succDegreePairTarget_of_closedSegmentCountEq
    (compatibleSuccDegreeClosedSegmentCountEqTarget_of_lowerCountEq hlower)

/-- Challenge-facing reduction from common-non-root succ-degree lower root
counts to the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_rootCountNonRoot
    (hcount : succDegreeRootCountNonRootTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hcount

/-- Challenge-facing reduction from the succ-degree constant-term branches to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_residual_and_lead
    (hlead : succDegreeRootCountLeadTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_residual_and_lead hlead hres

/-- Challenge-facing reduction from the residual branch, the both-nonzero lead
branch, and the right-zero `divX` orientation target to the repaired
succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_residual_bothNonzero_divXPrec
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget)
    (hres : succDegreeRootCountResidualTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_residual_bothNonzero_divX_prec
    hboth hdivX hres

/-- Challenge-facing reduction from the residual orientation target, the
both-nonzero lead branch, and the right-zero `divX` orientation target to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_residualPrec_bothNonzero_divXPrec
    (hresPrec : succDegreeRootCountResidualPrecTarget)
    (hboth : succDegreeRootCountLeadBothNonzeroTarget)
    (hdivX : succDegreeRootCountLeadRightZeroDivXPrecTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_residualPrec_bothNonzero_divX_prec
    hresPrec hboth hdivX

/-- Challenge-facing degree-zero base case for the succ-degree root-crossing
inequalities. -/
theorem succDegreeRootCrossingPair_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf_deg0 : f.natDegree = 0) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  succDegreeRootCrossing_of_natDegree_eq_zero hf_deg0

/-- Challenge-facing degree-zero base case for the succ-degree root-count
formulation. -/
theorem succDegreeRootCountPair_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_deg0 : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_natDegree_eq_zero hf hg hdeg hf_deg0 x

/-- Challenge-facing degree-zero base case for the upper-threshold succ-degree
root-count formulation. -/
theorem succDegreeRootCountAbovePair_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_deg0 : f.natDegree = 0) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_natDegree_eq_zero hf hg hdeg hf_deg0 x

/-- Challenge-facing degree-one base case for the upper-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountAbovePair_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg1 : f.natDegree = 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_posCombo_natDegree_eq_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg1 x

/-- Challenge-facing degree-one base case for the lower-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountPair_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg1 : f.natDegree = 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_posCombo_natDegree_eq_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg1 x

/-- Challenge-facing degree-one base case for the succ-degree root-crossing
inequalities in the positive-combination/no-common setting. -/
theorem succDegreeRootCrossingPair_of_posCombo_natDegree_eq_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg1 : f.natDegree = 1) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  succDegreeRootCrossing_of_posCombo_natDegree_eq_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg1

/-- Challenge-facing low-degree base case for the upper-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountAbovePair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 :=
  succDegreeRootCountAbove_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg_le_one x

/-- Challenge-facing low-degree base case for the lower-threshold succ-degree
root-count formulation in the positive-combination/no-common setting. -/
theorem succDegreeRootCountPair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg_le_one : f.natDegree ≤ 1) (x : ℝ) :
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg_le_one x

/-- Challenge-facing low-degree base case for the succ-degree root-crossing
inequalities in the positive-combination/no-common setting. -/
theorem succDegreeRootCrossingPair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf : f.Splits) (hf_deg_le_one : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) :=
  succDegreeRootCrossing_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf hf_deg_le_one

/-- Challenge-facing low-degree base case for succ-degree root-slot data in
the positive-combination/no-common setting. -/
theorem succDegreeSlotDataPair_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty :=
  succDegreeSlotData_of_posCombo_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_one

/-- Challenge-facing low-degree base case for the repaired succ-degree
common-right-interleaver endpoint in the positive-combination/no-common
setting. -/
theorem succDegreePairHasCommonInterleaver_of_posCombo_natDegree_le_one
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_le_one : f.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_natDegree_le_one
    hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_deg_le_one

/-- Challenge-facing degree-`≤ 2` no-common degree-split endpoint in the
positive-combination/nonnegative-coefficient setting. -/
theorem noCommonPairHasCommonInterleaver_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hg_deg_le_two : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
    hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hg_deg_le_two

/-- Challenge-facing unordered degree-bounded common-root reduction in the
positive-combination/nonnegative-coefficient setting.  It reduces the general
degree-`≤ N` pair endpoint to the no-common-root terminal case for ordered
close-degree pairs whose right degree is at most `N`. -/
theorem pairHasCommonInterleaver_nonneg_of_posCombo_natDegree_le_reduction
    {N : ℕ}
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        g.natDegree ≤ N →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hf_deg_le : f.natDegree ≤ N)
    (hg_deg_le : g.natDegree ≤ N) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered
    hterminal hf_pos hg_pos hfnn hgnn hfg hf_deg_le hg_deg_le

/-- Challenge-facing degree-`≤ 2` positive-combination endpoint in the
nonnegative-coefficient setting. -/
theorem pairHasCommonInterleaver_nonneg_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hf_deg_le_two : f.natDegree ≤ 2)
    (hg_deg_le_two : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_nonneg_of_posCombo_natDegree_le_reduction
    (N := 2)
    (fun {_f _g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    hf_pos hg_pos hfnn hgnn hfg hf_deg_le_two hg_deg_le_two

/-- Challenge-facing unordered degree-bounded common-root reduction in the
positive-combination/splitting setting.  It first translates to the
nonnegative-coefficient setting and then applies the nonnegative unordered
degree-bounded reduction. -/
theorem pairHasCommonInterleaver_of_posCombo_natDegree_le_reduction
    {N : ℕ}
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        g.natDegree ≤ N →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hf_deg_le : f.natDegree ≤ N)
    (hg_deg_le : g.natDegree ≤ N) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered_via_nonnegShift
    hterminal hf_pos hg_pos hf_splits hg_splits hfg hf_deg_le hg_deg_le

/-- Challenge-facing degree-`≤ 2` positive-combination endpoint. -/
theorem pairHasCommonInterleaver_of_posCombo_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hf_deg_le_two : f.natDegree ≤ 2)
    (hg_deg_le_two : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_posCombo_natDegree_le_reduction
    (N := 2)
    (fun {_f _g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    hf_pos hg_pos hf_splits hg_splits hfg hf_deg_le_two hg_deg_le_two

/-- Challenge-facing compatibility-level degree-`≤ 2` pair endpoint. -/
theorem compatiblePairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : Compatible f g)
    (hf_deg_le_two : f.natDegree ≤ 2)
    (hg_deg_le_two : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  RealRooted.compatiblePairHasCommonInterleaver_of_natDegree_le_two
    hf_pos hg_pos hfg hf_deg_le_two hg_deg_le_two

/-- Challenge-facing degree-zero base case for succ-degree root-slot data. -/
theorem succDegreeSlotDataPair_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    (f ≠ 0 ∧ f.Splits) ∧
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty :=
  succDegreeSlotData_of_natDegree_eq_zero
    hf_pos hg_pos hf_deg0 hsucc

/-- Challenge-facing degree-one analytic core for the succ-degree
root-crossing target. -/
theorem succDegreeRootLe_of_posCombo_deg1
    {α β γ : ℝ} (hβγ : γ ≤ β)
    (hsplit : ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (X - C α) + C μ * ((X - C β) * (X - C γ))).Splits) :
    γ ≤ α :=
  root_le_of_posCombo_deg1 hβγ hsplit

/-- Challenge-facing example showing that positive-combination real-rootedness
does not by itself force the stronger fixed succ-degree orientation. -/
theorem succDegree_deg1_positiveCombo_example :
    ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (C 2 * X + C 1) + C μ * ((X + C 1) * (X + C 2))).Splits :=
  posCombo_deg1_all_splits

/-- Challenge-facing counterexample to the fixed succ-degree orientation
shortcut. -/
theorem succDegree_deg1_not_prec_example :
    ¬ Prec (C 2 * X + C 1 : ℝ[X]) ((X + C 1) * (X + C 2)) :=
  not_prec_deg1_example

/-- Challenge-facing degree-zero base case for the repaired succ-degree
pair-interleaver endpoint. -/
theorem succDegreePairHasCommonInterleaver_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_deg0 : f.natDegree = 0)
    (hsucc : g.natDegree = f.natDegree + 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_degree_zero
    hf_pos hg_pos hf_deg0 hsucc

/-- Challenge-facing unconditional succ-degree left-splitting target from the
root-continuity endpoint. -/
theorem succDegreeLeftSplitsTarget_of_rootContinuity :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity

/-- Challenge-facing unconditional residual left-splitting target from the
root-continuity endpoint. -/
theorem succDegreeResidualLeftSplitsTarget_of_rootContinuity :
    succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_rootContinuity

/-- Challenge-facing reduction from left splitting and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_leftSplits_and_rootCrossing
    (hsplit : succDegreeLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_leftSplits_and_rootCrossing hsplit hcross

/-- Challenge-facing reduction from root crossing alone to succ-degree slot
data; root continuity supplies the left-splitting endpoint. -/
theorem succDegreeSlotDataTarget_of_rootCrossing
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_rootCrossing hcross

/-- Challenge-facing reduction from left splitting and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_leftSplits_and_rootCrossing
    (hsplit : succDegreeLeftSplitsTarget)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_leftSplits_and_rootCrossing
    hsplit hcross

/-- Challenge-facing reduction from root crossing alone to the repaired
succ-degree pair endpoint; root continuity supplies the left endpoint. -/
theorem succDegreePairTarget_of_rootCrossing
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hcross

/-- Challenge-facing PF/ASW reduction to the succ-degree left-splitting target. -/
theorem succDegreeLeftSplitsTarget_of_forward_asw
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw hASW

/-- Challenge-facing PF/ASW reduction to the residual left-splitting target. -/
theorem succDegreeResidualLeftSplitsTarget_of_forward_asw
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :
    succDegreeResidualLeftSplitsTarget :=
  PosComboSuccDegreeResidualLeftSplitsNonnegStatement_of_forward_asw hASW

/-- The zero-aware ASW target is equivalent to the splitting-only target. -/
theorem forwardASWTarget_iff_splitsTarget :
    (∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) ↔
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :=
  aissenSchoenbergWhitneyForwardOrZero_iff_splits

/-- Challenge-facing bridge from splitting-only ASW to the zero-aware ASW
target. -/
theorem forwardASWTarget_of_splitsTarget :
    (∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) →
    (∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0) :=
  aissenSchoenbergWhitneyForwardOrZero_of_splits

/-- Challenge-facing PF/ASW reduction to the succ-degree left-splitting target,
using only the splitting conjunct of ASW. -/
theorem succDegreeLeftSplitsTarget_of_forward_asw_splits
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :
    succDegreeLeftSplitsTarget :=
  PosComboSuccDegreeLeftSplitsNonnegStatement_of_forward_asw_splits hASW

/-- Challenge-facing PF/ASW reduction to the residual left-splitting target,
using only the splitting conjunct of ASW. -/
theorem succDegreeResidualLeftSplitsTarget_of_forward_asw_splits
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits) :
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
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from splitting-only ASW and root crossing to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_splits_and_rootCrossing
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from forward ASW and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_and_rootCrossing
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0)
    (hcross : succDegreeRootCrossingTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_rootCrossing
    hASW hcross

/-- Challenge-facing reduction from splitting-only ASW and root crossing to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_splits_and_rootCrossing
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
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
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_and_orientation
    hASW horient

/-- Challenge-facing reduction from splitting-only ASW and fixed orientation to
succ-degree slot data. -/
theorem succDegreeSlotDataTarget_of_forward_asw_splits_and_orientation
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (horient : succDegreeOrientationTarget) :
    succDegreeSlotDataTarget :=
  posComboNoCommonSuccDegreeSlotData_of_forward_asw_splits_and_orientation
    hASW horient

/-- Challenge-facing reduction from forward ASW and fixed orientation to the
repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_and_orientation
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0)
    (horient : succDegreeOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_forward_asw_and_orientation
    hASW horient

/-- Challenge-facing reduction from splitting-only ASW and fixed orientation to
the repaired succ-degree pair endpoint. -/
theorem succDegreePairTarget_of_forward_asw_splits_and_orientation
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
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
    (haff : affineFamilyTarget) :
    succDegreePairTarget :=
  posComboNoCommonSuccDegreePairHasCommonInterleaver_of_affineFamily haff

/-- Challenge-facing reduction from boundary-right-pair orientation to the
affine-family bridge. -/
theorem affineFamilyTarget_of_boundaryRight
    (hboundary : boundaryRightPairOrientationTarget) :
    affineFamilyTarget :=
  posComboNoCommonAffineFamily_of_boundaryRightPairOrientation hboundary

/-- Challenge-facing no-common left-endpoint reduction from the affine-family
bridge.  This is the endpoint part of `succDegreePairTarget_of_affineFamily`;
the remaining input is producing the affine family from positive
compatibility. -/
theorem succDegreeNoCommonLeftSplitsTarget_of_affineFamily
    (haff : affineFamilyTarget)
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
    (hboundary : boundaryRightPairOrientationTarget)
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
    (hboundary : boundaryRightPairOrientationTarget) :
    succDegreePairTarget :=
  succDegreePairHasCommonInterleaver_nonneg_of_boundaryRightPairOrientation
    hboundary

/-- Full roadmap reduction for the common-left target. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge
    (_htwo : compatiblePairHasCommonLeftInterleaverTarget)
    (hglobal : _root_.RealRooted.CommonLeftInterleaverFamilyUpgradeStatement) :
    commonLeftInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    hglobal

/-- Direct roadmap reduction for the common-left target after the finite-family
common-left upgrade has been internalized. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge_direct
    (_htwo : compatiblePairHasCommonLeftInterleaverTarget) :
    commonLeftInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct

/-- Full roadmap reduction for the common-right target. -/
theorem commonInterleaverTarget_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    commonInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge htwo

/-- Challenge-facing pairwise upgrade from lower-threshold root-count
formulations alone. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCount
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from same-degree lower-threshold root
counts and succ-degree upper-threshold root counts. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAbove
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAbove
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from same-degree upper-threshold root
counts and succ-degree lower-threshold root counts. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAbove
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAbove
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from upper-threshold root-count
formulations in both branches. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBoth
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from common-non-root lower-threshold
root-count formulations in both branches. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountNonRoot
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountNonRoot
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from same-degree common-non-root
lower-threshold root counts and succ-degree common-non-root upper-threshold
root counts. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveNonRoot
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveNonRoot
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from same-degree common-non-root
upper-threshold root counts and succ-degree common-non-root lower-threshold
root counts. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAboveNonRoot
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_sameRootCountAboveNonRoot
    hsame hsucc hpos hpair

/-- Challenge-facing pairwise upgrade from common-non-root upper-threshold
root-count formulations in both branches. -/
theorem
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBothNonRoot
    {fs : List ℝ[X]}
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_rootCountAboveBothNonRoot
    hsame hsucc hpos hpair

/-- Challenge-facing full roadmap reduction from the root-crossing
formulations alone; root continuity supplies the succ-degree left endpoint. -/
theorem commonInterleaverTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_direct
    hsame hsucc

/-- Challenge-facing full roadmap reduction from lower-threshold root-count
formulations alone. -/
theorem commonInterleaverTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCount hsame hsucc)

/-- Challenge-facing full roadmap reduction from same-degree lower-threshold
root counts and succ-degree upper-threshold root counts. -/
theorem commonInterleaverTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCountAbove hsame hsucc)

/-- Challenge-facing full roadmap reduction from same-degree upper-threshold
root counts and succ-degree lower-threshold root counts. -/
theorem commonInterleaverTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_sameRootCountAbove hsame hsucc)

/-- Challenge-facing full roadmap reduction from upper-threshold root-count
formulations in both the same-degree and succ-degree branches. -/
theorem commonInterleaverTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCountAboveBoth hsame hsucc)

/-- Challenge-facing full roadmap reduction from common-non-root lower-threshold
root-count formulations in both branches. -/
theorem commonInterleaverTarget_of_rootCountNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCountNonRoot hsame hsucc)

/-- Challenge-facing full roadmap reduction from same-degree common-non-root
lower-threshold root counts and succ-degree common-non-root upper-threshold
root counts. -/
theorem commonInterleaverTarget_of_rootCountAboveNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot hsame hsucc)

/-- Challenge-facing full roadmap reduction from same-degree common-non-root
upper-threshold root counts and succ-degree common-non-root lower-threshold
root counts. -/
theorem commonInterleaverTarget_of_sameRootCountAboveNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_sameRootCountAboveNonRoot hsame hsucc)

/-- Challenge-facing full roadmap reduction from common-non-root upper-threshold
root-count formulations in both branches. -/
theorem commonInterleaverTarget_of_rootCountAboveBothNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    commonInterleaverTarget :=
  commonInterleaverTarget_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_rootCountAboveBothNonRoot hsame hsucc)

/-- Challenge-facing full roadmap reduction from the root-crossing formulations,
with the succ-degree left endpoint supplied by forward ASW. -/
theorem commonInterleaverTarget_of_rootCrossing_and_forward_asw
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forward_asw
    hsame hASW hsucc

/-- Challenge-facing full roadmap reduction from the root-crossing formulations,
with the succ-degree left endpoint supplied by the splitting-only ASW target. -/
theorem commonInterleaverTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (hsucc : succDegreeRootCrossingTarget) :
  commonInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forwardASWSplits
    hsame hASW hsucc

/-- Challenge-facing full roadmap reduction from same-degree root-crossing and
the affine-family bridge for the succ-degree branch. -/
theorem commonInterleaverTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    commonInterleaverTarget :=
  chudnovskySeymour_commonInterleaver_of_sameDegreeCrossing_affineFamily
    hsame haff

/-- Challenge-facing projection from the common-right target to the full
finite-family compatibility target. -/
theorem familyCompatibleTarget_of_commonInterleaverTarget
    (hcommon : commonInterleaverTarget) :
    familyCompatibleTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    hcommon

/-- Challenge-facing full finite-family compatibility reduction from the
natural two-polynomial common-interleaver bridge. -/
theorem familyCompatibleTarget_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_pairBridge htwo)

/-- Challenge-facing finite-family compatibility reduction from the
root-crossing formulations alone. -/
theorem familyCompatibleTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCrossing hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from lower-threshold
root-count formulations alone. -/
theorem familyCompatibleTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCount hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from same-degree
lower-threshold root counts and succ-degree upper-threshold root counts. -/
theorem familyCompatibleTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCountAbove hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from same-degree
upper-threshold root counts and succ-degree lower-threshold root counts. -/
theorem familyCompatibleTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_sameRootCountAbove hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from upper-threshold
root-count formulations in both branches. -/
theorem familyCompatibleTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCountAboveBoth hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from common-non-root
lower-threshold root-count formulations in both branches. -/
theorem familyCompatibleTarget_of_rootCountNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCountNonRoot hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from same-degree
common-non-root lower counts and succ-degree common-non-root upper counts. -/
theorem familyCompatibleTarget_of_rootCountAboveNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCountAboveNonRoot hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from same-degree
common-non-root upper counts and succ-degree common-non-root lower counts. -/
theorem familyCompatibleTarget_of_sameRootCountAboveNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_sameRootCountAboveNonRoot hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from common-non-root
upper-threshold root-count formulations in both branches. -/
theorem familyCompatibleTarget_of_rootCountAboveBothNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCountAboveBothNonRoot hsame hsucc)

/-- Challenge-facing finite-family compatibility reduction from root-crossing
with the succ-degree left endpoint supplied by forward ASW. -/
theorem familyCompatibleTarget_of_rootCrossing_and_forward_asw
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, HasNonnegCoeffs p → IsPolyaFreqSeq (fun n ↦ p.coeff n) →
      (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0)
    (hsucc : succDegreeRootCrossingTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCrossing_and_forward_asw hsame hASW hsucc)

/-- Challenge-facing finite-family compatibility reduction from root-crossing
with the succ-degree left endpoint supplied by splitting-only ASW. -/
theorem familyCompatibleTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (hsucc : succDegreeRootCrossingTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_rootCrossing_and_forward_asw_splits
      hsame hASW hsucc)

/-- Challenge-facing finite-family compatibility reduction from same-degree
root-crossing and the affine-family bridge for the succ-degree branch. -/
theorem familyCompatibleTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    familyCompatibleTarget :=
  familyCompatibleTarget_of_commonInterleaverTarget
    (commonInterleaverTarget_of_sameDegreeRootCrossing_and_affineFamily
      hsame haff)

/-- Challenge-facing four-way package from the root-crossing formulations
alone; root continuity supplies the succ-degree left endpoint. -/
theorem fourWay_of_rootCrossing
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing
    hrr hpos hsame hsucc

/-- Challenge-facing four-way package from lower-threshold root-count
formulations alone. -/
theorem fourWay_of_rootCount
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing four-way package from same-degree lower-threshold root
counts and succ-degree upper-threshold root counts. -/
theorem fourWay_of_rootCountAbove
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing four-way package from same-degree upper-threshold root
counts and succ-degree lower-threshold root counts. -/
theorem fourWay_of_sameRootCountAbove
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing four-way package from upper-threshold root-count
formulations in both branches. -/
theorem fourWay_of_rootCountAboveBoth
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayPackage fs :=
  fourWay_of_rootCrossing hrr hpos
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing four-way package from the root-crossing formulations,
with the succ-degree left endpoint supplied by the splitting-only ASW target. -/
theorem fourWay_of_rootCrossing_and_forward_asw_splits
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw_splits
    hrr hpos hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative four-way target from
root-crossing alone. -/
theorem fourWayNonnegCoeffsTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative four-way target from
lower-threshold root-count formulations alone. -/
theorem fourWayNonnegCoeffsTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree lower-threshold root counts and succ-degree upper-threshold root
counts. -/
theorem fourWayNonnegCoeffsTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree upper-threshold root counts and succ-degree lower-threshold root
counts. -/
theorem fourWayNonnegCoeffsTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
upper-threshold root-count formulations in both branches. -/
theorem fourWayNonnegCoeffsTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
common-non-root lower-threshold root-count formulations in both branches. -/
theorem fourWayNonnegCoeffsTarget_of_rootCountNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree common-non-root lower-threshold root counts and succ-degree
common-non-root upper-threshold root counts. -/
theorem fourWayNonnegCoeffsTarget_of_rootCountAboveNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree common-non-root upper-threshold root counts and succ-degree
common-non-root lower-threshold root counts. -/
theorem fourWayNonnegCoeffsTarget_of_sameRootCountAboveNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
common-non-root upper-threshold root-count formulations in both branches. -/
theorem fourWayNonnegCoeffsTarget_of_rootCountAboveBothNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative four-way target from
root-crossing plus splitting-only ASW. -/
theorem fourWayNonnegCoeffsTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (hsucc : succDegreeRootCrossingTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
    hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative four-way target from
same-degree root-crossing and the affine-family bridge. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative four-way target from the
no-common orientation core. -/
theorem fourWayNonnegCoeffsTarget_of_noCommonOrientation
    (hstep : noCommonOrientationTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_noCommonOrientation_nonneg hstep

/-- Challenge-facing reduction for the nonnegative four-way target from the
repaired same-degree bridge and affine-family successor-degree bridge. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreePair_and_affineFamily
    (hsame : sameDegreePairTarget)
    (haff : affineFamilyTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWayTarget_of_sameDegreePair_and_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative four-way target from the
all-combinations bridge. -/
theorem fourWayNonnegCoeffsTarget_of_allComboBridge
    (hall : allComboBridgeTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_allComboBridge_nonneg hall

/-- Challenge-facing reduction for the nonnegative four-way target from the
affine-family bridge. -/
theorem fourWayNonnegCoeffsTarget_of_affineFamilyBridge
    (haff : affineFamilyTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_affineFamilyBridge_nonneg haff

/-- Challenge-facing reduction for the nonnegative common-right target from
root-crossing alone. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_commonInterleaver_of_rootCrossing_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative common-right target from
lower-threshold root-count formulations alone. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree lower-threshold root counts and succ-degree upper-threshold root
counts. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree upper-threshold root counts and succ-degree lower-threshold root
counts. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
upper-threshold root-count formulations in both branches. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
common-non-root lower-threshold root-count formulations in both branches. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCountNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree common-non-root lower-threshold root counts and succ-degree
common-non-root upper-threshold root counts. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCountAboveNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree common-non-root upper-threshold root counts and succ-degree
common-non-root lower-threshold root counts. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameRootCountAboveNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
common-non-root upper-threshold root-count formulations in both branches. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCountAboveBothNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative common-right target from
root-crossing plus splitting-only ASW. -/
theorem commonInterleaverNonnegCoeffsTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (hsucc : succDegreeRootCrossingTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_commonInterleaver_of_rootCrossing_forwardASWSplits_nonneg
    hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative common-right target from
same-degree root-crossing and the affine-family bridge. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative common-right target from the
no-common orientation core. -/
theorem commonInterleaverNonnegCoeffsTarget_of_noCommonOrientation
    (hstep : noCommonOrientationTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_noCommonOrientation_nonneg
    hstep

/-- Challenge-facing reduction for the nonnegative common-right target from the
repaired same-degree bridge and affine-family successor-degree bridge. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_affineFamily
    (hsame : sameDegreePairTarget)
    (haff : affineFamilyTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative common-right target from the
all-combinations bridge. -/
theorem commonInterleaverNonnegCoeffsTarget_of_allComboBridge
    (hall : allComboBridgeTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_allComboBridge_nonneg
    hall

/-- Challenge-facing reduction for the nonnegative common-right target from the
affine-family bridge. -/
theorem commonInterleaverNonnegCoeffsTarget_of_affineFamilyBridge
    (haff : affineFamilyTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_affineFamilyBridge_nonneg
    haff

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from root-crossing alone. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (hsame : sameDegreeRootCrossingTarget)
    (hsucc : succDegreeRootCrossingTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_familyCompatible_of_rootCrossing_nonneg hsame hsucc

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from lower-threshold root-count formulations alone. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCount
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree lower-threshold root counts and succ-degree
upper-threshold root counts. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCountAbove
    (hsame : sameDegreeRootCountTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCount hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree upper-threshold root counts and succ-degree
lower-threshold root counts. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameRootCountAbove
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCount hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from upper-threshold root-count formulations in both branches. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCountAboveBoth
    (hsame : sameDegreeRootCountAboveTarget)
    (hsucc : succDegreeRootCountAboveTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAbove hsame)
    (succDegreeRootCrossingTarget_of_rootCountAbove hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from common-non-root lower-threshold root-count formulations in both
branches. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCountNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree common-non-root lower-threshold root counts and
succ-degree common-non-root upper-threshold root counts. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCountAboveNonRoot
    (hsame : sameDegreeRootCountNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree common-non-root upper-threshold root counts and
succ-degree common-non-root lower-threshold root counts. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameRootCountAboveNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountNonRootTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from common-non-root upper-threshold root-count formulations in both
branches. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCountAboveBothNonRoot
    (hsame : sameDegreeRootCountAboveNonRootTarget)
    (hsucc : succDegreeRootCountAboveNonRootTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_rootCrossing
    (sameDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsame)
    (succDegreeRootCrossingTarget_of_rootCountAboveNonRoot hsucc)

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from root-crossing plus splitting-only ASW. -/
theorem familyCompatibleNonnegCoeffsTarget_of_rootCrossing_and_forward_asw_splits
    (hsame : sameDegreeRootCrossingTarget)
    (hASW : ∀ {p : ℝ[X]}, IsPolyaFreqSeq (fun n ↦ p.coeff n) → p.Splits)
    (hsucc : succDegreeRootCrossingTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_familyCompatible_of_rootCrossing_forwardASWSplits_nonneg
    hsame hASW hsucc

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from same-degree root-crossing and the affine-family bridge. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_affineFamily
    (hsame : sameDegreeRootCrossingTarget)
    (haff : affineFamilyTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from the no-common orientation core. -/
theorem familyCompatibleNonnegCoeffsTarget_of_noCommonOrientation
    (hstep : noCommonOrientationTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_noCommonOrientation_nonneg
    hstep

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from the repaired same-degree bridge and affine-family successor-degree
bridge. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_affineFamily
    (hsame : sameDegreePairTarget)
    (haff : affineFamilyTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_affineFamily_nonneg
    hsame haff

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from the all-combinations bridge. -/
theorem familyCompatibleNonnegCoeffsTarget_of_allComboBridge
    (hall : allComboBridgeTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_allComboBridge_nonneg
    hall

/-- Challenge-facing reduction for the nonnegative finite-family compatibility
target from the affine-family bridge. -/
theorem familyCompatibleNonnegCoeffsTarget_of_affineFamilyBridge
    (haff : affineFamilyTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_nonneg
    haff

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
    (hboundary : boundaryRightPairOrientationTarget) :
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
    (hboundary : boundaryRightPairOrientationTarget) :
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
    (hboundary : boundaryRightPairOrientationTarget) :
    fourWayNonnegCoeffsTarget :=
  chudnovskySeymour_fourWay_of_boundaryRight_nonneg hboundary

/-! ### Composition wrappers combining the #41 same-degree endpoint with the
#42 closed-segment/lower-count route -/

/-- Nonnegative-coefficient common-right target from the #41 same-degree pair
endpoint and the #42 compatible closed-segment endpoint count equality. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (hsame : sameDegreePairTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_pairDegreeSplit hsame
    (succDegreePairTarget_of_closedSegmentCountEq hcount)

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree pair endpoint and the #42 compatible closed-segment endpoint count
equality. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (hsame : sameDegreePairTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_pairDegreeSplit hsame
    (succDegreePairTarget_of_closedSegmentCountEq hcount)

/-- Nonnegative four-way package target from the #41 same-degree pair endpoint
and the #42 compatible closed-segment endpoint count equality. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (hsame : sameDegreePairTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_pairDegreeSplit hsame
    (succDegreePairTarget_of_closedSegmentCountEq hcount)

/-- Nonnegative-coefficient common-right target from the #41 same-degree pair
endpoint and the #42 compatible succ-degree exact lower-threshold endpoint-sign
count equality leaf. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (hsame : sameDegreePairTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq hsame
    (compatibleSuccDegreeClosedSegmentCountEqTarget_of_lowerCountEq hlower)

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree pair endpoint and the #42 compatible succ-degree exact
lower-threshold endpoint-sign count equality leaf. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (hsame : sameDegreePairTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq hsame
    (compatibleSuccDegreeClosedSegmentCountEqTarget_of_lowerCountEq hlower)

/-- Nonnegative four-way package target from the #41 same-degree pair endpoint
and the #42 compatible succ-degree exact lower-threshold endpoint-sign count
equality leaf. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (hsame : sameDegreePairTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq hsame
    (compatibleSuccDegreeClosedSegmentCountEqTarget_of_lowerCountEq hlower)

/-! #### Same-degree slot-data endpoint (#41) with the direct #42 route

The same-degree slot-data endpoint feeds the repaired same-degree pair endpoint
through `sameDegreePairTarget_of_slotData`, so these wrappers only precompose
that reduction with the pair-endpoint wrappers above. -/

/-- Nonnegative-coefficient common-right target from the #41 same-degree
slot-data endpoint and the #42 compatible closed-segment count equality. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeSlotData_and_closedSegmentCountEq
    (hslot : sameDegreeSlotDataTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (sameDegreePairTarget_of_slotData hslot) hcount

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree slot-data endpoint and the #42 closed-segment count equality. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeSlotData_and_closedSegmentCountEq
    (hslot : sameDegreeSlotDataTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (sameDegreePairTarget_of_slotData hslot) hcount

/-- Nonnegative four-way package target from the #41 same-degree slot-data
endpoint and the #42 compatible closed-segment count equality. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeSlotData_and_closedSegmentCountEq
    (hslot : sameDegreeSlotDataTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (sameDegreePairTarget_of_slotData hslot) hcount

/-- Nonnegative-coefficient common-right target from the #41 same-degree
slot-data endpoint and the #42 endpoint-sign lower-count equality. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeSlotData_and_lowerCountEq
    (hslot : sameDegreeSlotDataTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (sameDegreePairTarget_of_slotData hslot) hlower

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree slot-data endpoint and the #42 endpoint-sign lower-count equality. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeSlotData_and_lowerCountEq
    (hslot : sameDegreeSlotDataTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (sameDegreePairTarget_of_slotData hslot) hlower

/-- Nonnegative four-way package target from the #41 same-degree slot-data
endpoint and the #42 endpoint-sign lower-count equality. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeSlotData_and_lowerCountEq
    (hslot : sameDegreeSlotDataTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (sameDegreePairTarget_of_slotData hslot) hlower

/-! #### Same-degree root-crossing endpoint (#41) with the direct #42 route

The same-degree root-crossing endpoint reduces to the repaired same-degree pair
endpoint via `sameDegreePairTarget_of_rootCrossing`. -/

/-- Nonnegative-coefficient common-right target from the #41 same-degree
root-crossing endpoint and the #42 compatible closed-segment count equality. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_closedSegmentCountEq
    (hcross : sameDegreeRootCrossingTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (sameDegreePairTarget_of_rootCrossing hcross) hcount

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree root-crossing endpoint and the #42 closed-segment count equality. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_closedSegmentCountEq
    (hcross : sameDegreeRootCrossingTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (sameDegreePairTarget_of_rootCrossing hcross) hcount

/-- Nonnegative four-way package target from the #41 same-degree root-crossing
endpoint and the #42 compatible closed-segment count equality. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_closedSegmentCountEq
    (hcross : sameDegreeRootCrossingTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_sameDegreePair_and_closedSegmentCountEq
    (sameDegreePairTarget_of_rootCrossing hcross) hcount

/-- Nonnegative-coefficient common-right target from the #41 same-degree
root-crossing endpoint and the #42 endpoint-sign lower-count equality. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_lowerCountEq
    (hcross : sameDegreeRootCrossingTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (sameDegreePairTarget_of_rootCrossing hcross) hlower

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree root-crossing endpoint and the #42 endpoint-sign lower-count equality. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_lowerCountEq
    (hcross : sameDegreeRootCrossingTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (sameDegreePairTarget_of_rootCrossing hcross) hlower

/-- Nonnegative four-way package target from the #41 same-degree root-crossing
endpoint and the #42 endpoint-sign lower-count equality. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_lowerCountEq
    (hcross : sameDegreeRootCrossingTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_sameDegreePair_and_lowerCountEq
    (sameDegreePairTarget_of_rootCrossing hcross) hlower

/-! #### Same-degree lower root-count endpoint (#41) with the direct #42 route

The same-degree lower-threshold root-count endpoint reduces to the same-degree
root-crossing endpoint via `sameDegreeRootCrossingTarget_of_rootCount`. -/

/-- Nonnegative-coefficient common-right target from the #41 same-degree lower
root-count endpoint and the #42 compatible closed-segment count equality. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCount_and_closedSegmentCountEq
    (hrc : sameDegreeRootCountTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_closedSegmentCountEq
    (sameDegreeRootCrossingTarget_of_rootCount hrc) hcount

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree lower root-count endpoint and the #42 closed-segment count equality. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCount_and_closedSegmentCountEq
    (hrc : sameDegreeRootCountTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_closedSegmentCountEq
    (sameDegreeRootCrossingTarget_of_rootCount hrc) hcount

/-- Nonnegative four-way package target from the #41 same-degree lower
root-count endpoint and the #42 compatible closed-segment count equality. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeRootCount_and_closedSegmentCountEq
    (hrc : sameDegreeRootCountTarget)
    (hcount : compatibleSuccDegreeClosedSegmentCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_closedSegmentCountEq
    (sameDegreeRootCrossingTarget_of_rootCount hrc) hcount

/-- Nonnegative-coefficient common-right target from the #41 same-degree lower
root-count endpoint and the #42 endpoint-sign lower-count equality. -/
theorem commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCount_and_lowerCountEq
    (hrc : sameDegreeRootCountTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    commonInterleaverNonnegCoeffsTarget :=
  commonInterleaverNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_lowerCountEq
    (sameDegreeRootCrossingTarget_of_rootCount hrc) hlower

/-- Nonnegative-coefficient finite-family compatibility target from the #41
same-degree lower root-count endpoint and the #42 endpoint-sign lower-count equality. -/
theorem familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCount_and_lowerCountEq
    (hrc : sameDegreeRootCountTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  familyCompatibleNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_lowerCountEq
    (sameDegreeRootCrossingTarget_of_rootCount hrc) hlower

/-- Nonnegative four-way package target from the #41 same-degree lower
root-count endpoint and the #42 endpoint-sign lower-count equality. -/
theorem fourWayNonnegCoeffsTarget_of_sameDegreeRootCount_and_lowerCountEq
    (hrc : sameDegreeRootCountTarget)
    (hlower : compatibleSuccDegreeEndpointSignLowerCountEqTarget) :
    fourWayNonnegCoeffsTarget :=
  fourWayNonnegCoeffsTarget_of_sameDegreeRootCrossing_and_lowerCountEq
    (sameDegreeRootCrossingTarget_of_rootCount hrc) hlower

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

/-- Challenge-facing degree-`≤ 2` four-way Chudnovsky--Seymour package under
the standard memberwise real-rootedness hypothesis. -/
theorem fourWay_of_natDegree_le_two {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    fourWayPackage fs :=
  chudnovskySeymour_fourWay_of_natDegree_le_two
    (fs := fs) hrr hpos hdeg

/-- Solved low-degree pairwise compatibility / pairwise common-interleaver
equivalence. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing degree-`≤ 2` pairwise compatibility / pairwise
common-interleaver equivalence. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_natDegree_le_two
    hpos hdeg

/-- Solved low-degree pairwise common-interleaver / global common-interleaver
equivalence. -/
theorem pairwiseHasCommonInterleaver_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing degree-`≤ 2` pairwise common-interleaver / global common
interleaver equivalence under memberwise real-rootedness. -/
theorem pairwiseHasCommonInterleaver_iff_commonInterleaver_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_natDegree_le_two
    hrr hpos hdeg

/-- Solved low-degree global common-interleaver / full-family compatibility
equivalence. -/
theorem commonInterleaver_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  RealRooted.hasCommonInterleaver_iff_familyCompatible_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing degree-`≤ 2` global common-interleaver / full-family
compatibility equivalence under memberwise real-rootedness. -/
theorem commonInterleaver_iff_familyCompatible_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  RealRooted.hasCommonInterleaver_iff_familyCompatible_of_natDegree_le_two
    hrr hpos hdeg

/-- Solved low-degree pairwise/common-interleaver equivalence. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing degree-`≤ 2` pairwise/common-interleaver equivalence under
memberwise real-rootedness. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_two
    hrr hpos hdeg

/-- Solved low-degree pairwise/common-left-interleaver equivalence. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_natDegree_le_one
    hpos hdeg

/-- Solved low-degree pairwise/full-family compatibility equivalence. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing degree-`≤ 2` pairwise/full-family compatibility
equivalence under memberwise real-rootedness. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_two
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 2) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  RealRooted.pairwiseCompatible_iff_familyCompatible_of_natDegree_le_two
    hrr hpos hdeg

/-- Challenge-facing reduction for the left-oriented common-interleaver target. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (_htwo : compatiblePairHasCommonLeftInterleaverTarget)
    (hglobal : PairwiseHasCommonLeftInterleaver fs → HasCommonLeftInterleaver fs) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    hpos hglobal

/-- Challenge-facing direct left-oriented finite-family reduction after the
common-left upgrade: only the two-polynomial common-left bridge remains. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (_htwo : compatiblePairHasCommonLeftInterleaverTarget) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    hrr hpos

/-! ## Same-degree orientation alternative counterexample -/

/- The strong orientation-alternative endpoint is false already in degree two.
The nested pair `(X + 6)(X + 1)` and `(X + 2)(X + 3)` has nonnegative
coefficients, positive leading coefficients, no common root, and every positive
combination is real-rooted.  The roots are nested, so neither orientation
`Prec f g` nor `Prec g f` holds. -/

/-- Outer quadratic `(X + 6)(X + 1)` of the degree-two counterexample. -/
private def orientAltCexA : ℝ[X] := (X + C 6) * (X + C 1)

/-- Inner quadratic `(X + 2)(X + 3)` of the degree-two counterexample. -/
private def orientAltCexB : ℝ[X] := (X + C 2) * (X + C 3)

private lemma orientAltCexA_monic : orientAltCexA.Monic :=
  (Polynomial.monic_X_add_C 6).mul (Polynomial.monic_X_add_C 1)

private lemma orientAltCexB_monic : orientAltCexB.Monic :=
  (Polynomial.monic_X_add_C 2).mul (Polynomial.monic_X_add_C 3)

private lemma orientAltCexA_natDegree : orientAltCexA.natDegree = 2 := by
  unfold orientAltCexA
  rw [Polynomial.natDegree_mul
    (Polynomial.X_add_C_ne_zero 6) (Polynomial.X_add_C_ne_zero 1),
    Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C]

private lemma orientAltCexB_natDegree : orientAltCexB.natDegree = 2 := by
  unfold orientAltCexB
  rw [Polynomial.natDegree_mul
    (Polynomial.X_add_C_ne_zero 2) (Polynomial.X_add_C_ne_zero 3),
    Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_add_C]

private lemma orientAltCexA_posLeading : HasPosLeadingCoeff orientAltCexA := by
  change (0 : ℝ) < orientAltCexA.leadingCoeff
  rw [orientAltCexA_monic.leadingCoeff]
  norm_num

private lemma orientAltCexB_posLeading : HasPosLeadingCoeff orientAltCexB := by
  change (0 : ℝ) < orientAltCexB.leadingCoeff
  rw [orientAltCexB_monic.leadingCoeff]
  norm_num

private lemma orientAltCexA_nextCoeff : orientAltCexA.nextCoeff = 7 := by
  unfold orientAltCexA
  rw [(Polynomial.monic_X_add_C (6 : ℝ)).nextCoeff_mul
      (Polynomial.monic_X_add_C (1 : ℝ)),
    Polynomial.nextCoeff_X_add_C, Polynomial.nextCoeff_X_add_C]
  norm_num

private lemma orientAltCexB_nextCoeff : orientAltCexB.nextCoeff = 5 := by
  unfold orientAltCexB
  rw [(Polynomial.monic_X_add_C (2 : ℝ)).nextCoeff_mul
      (Polynomial.monic_X_add_C (3 : ℝ)),
    Polynomial.nextCoeff_X_add_C, Polynomial.nextCoeff_X_add_C]
  norm_num

private lemma orientAltCexA_nonneg : HasNonnegCoeffs orientAltCexA := by
  have hexp : orientAltCexA = C 6 + C 7 * X + X ^ 2 := by
    apply Polynomial.funext
    intro x
    simp only [orientAltCexA, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  intro n
  rw [hexp]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  split_ifs <;> norm_num

private lemma orientAltCexB_nonneg : HasNonnegCoeffs orientAltCexB := by
  have hexp : orientAltCexB = C 6 + C 5 * X + X ^ 2 := by
    apply Polynomial.funext
    intro x
    simp only [orientAltCexB, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  intro n
  rw [hexp]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  split_ifs <;> norm_num

private lemma orientAltCexA_neg_one_mem : (-1 : ℝ) ∈ orientAltCexA.roots := by
  unfold orientAltCexA
  rw [Polynomial.roots_mul
      (mul_ne_zero (Polynomial.X_add_C_ne_zero 6) (Polynomial.X_add_C_ne_zero 1)),
    Polynomial.roots_X_add_C, Polynomial.roots_X_add_C, Multiset.mem_add]
  right
  rw [Multiset.mem_singleton]

private lemma orientAltCexB_roots_le :
    ∀ r ∈ orientAltCexB.roots, r ≤ -2 := by
  unfold orientAltCexB
  rw [Polynomial.roots_mul
      (mul_ne_zero (Polynomial.X_add_C_ne_zero 2) (Polynomial.X_add_C_ne_zero 3)),
    Polynomial.roots_X_add_C, Polynomial.roots_X_add_C]
  intro r hr
  simp only [Multiset.mem_add, Multiset.mem_singleton] at hr
  rcases hr with h | h <;> subst h <;> norm_num

private lemma orientAltCex_noCommon :
    ∀ r, orientAltCexA.IsRoot r → ¬ orientAltCexB.IsRoot r := by
  intro r hrA hrB
  simp only [orientAltCexA, Polynomial.IsRoot.def, eval_mul, eval_add, eval_X,
    eval_C, mul_eq_zero] at hrA
  simp only [orientAltCexB, Polynomial.IsRoot.def, eval_mul, eval_add, eval_X,
    eval_C, mul_eq_zero] at hrB
  rcases hrA with h | h <;> rcases hrB with h' | h' <;> linarith

private lemma orientAltCex_posCombo :
    PosComboRealRooted orientAltCexA orientAltCexB := by
  intro lam μ hlam hμ
  have hexp : C lam * orientAltCexA + C μ * orientAltCexB =
      C (lam + μ) * X ^ 2 + C (7 * lam + 5 * μ) * X + C (6 * lam + 6 * μ) := by
    apply Polynomial.funext
    intro x
    simp only [orientAltCexA, orientAltCexB, eval_add, eval_mul, eval_C, eval_X,
      eval_pow]
    ring
  rw [hexp]
  have hlc : (0 : ℝ) < lam + μ := by linarith
  set q : ℝ[X] :=
    C (lam + μ) * X ^ 2 + C (7 * lam + 5 * μ) * X + C (6 * lam + 6 * μ) with hq
  have hc2 : q.coeff 2 = lam + μ := by
    rw [hq]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  have hc1 : q.coeff 1 = 7 * lam + 5 * μ := by
    rw [hq]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  have hc0 : q.coeff 0 = 6 * lam + 6 * μ := by
    rw [hq]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  have hdeg : q.natDegree = 2 := by
    rw [hq]
    exact Polynomial.natDegree_quadratic hlc.ne'
  have hdisc : 0 ≤ discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
    rw [hc2, hc1, hc0]
    have hd :
        discrim (lam + μ) (7 * lam + 5 * μ) (6 * lam + 6 * μ) =
          25 * lam ^ 2 + 22 * lam * μ + μ ^ 2 := by
      unfold discrim
      ring
    rw [hd]
    nlinarith [mul_pos hlam hμ, sq_nonneg lam, sq_nonneg μ]
  exact Polynomial.isRealRooted_of_natDegree_two_of_discrim_nonneg hdeg hdisc

/-- The strong same-degree orientation alternative is false. -/
theorem not_posComboNoCommonSameDegreeOrientationAlternativeNonneg :
    ¬ PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement := by
  intro H
  have hor := H orientAltCexA_posLeading orientAltCexB_posLeading
    orientAltCexA_nonneg orientAltCexB_nonneg orientAltCex_posCombo
    (by rw [orientAltCexB_natDegree, orientAltCexA_natDegree])
    orientAltCex_noCommon
  rcases hor with hAB | hBA
  · have h := roots_le_of_prec_right hAB orientAltCexB_roots_le
    have hbad := h (-1) orientAltCexA_neg_one_mem
    norm_num at hbad
  · have h := nextCoeff_le_of_prec_sameDegree_monic
      orientAltCexB_monic orientAltCexA_monic hBA
      (by rw [orientAltCexB_natDegree, orientAltCexA_natDegree])
    rw [orientAltCexA_nextCoeff, orientAltCexB_nextCoeff] at h
    norm_num at h

/-- Challenge-facing falsity of the strong same-degree orientation alternative. -/
theorem not_sameDegreeOrientationAlternativeTarget :
    ¬ sameDegreeOrientationAlternativeTarget :=
  not_posComboNoCommonSameDegreeOrientationAlternativeNonneg

/-! ## Direct issue #42 route: harvested succ-degree support -/

/-- Challenge-facing lower-degree succ-degree endpoint splitting. -/
theorem succDegreeLeftEndpointSplits {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  RealRooted.left_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Challenge-facing higher-degree succ-degree endpoint splitting. -/
theorem succDegreeRightEndpointSplits {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  RealRooted.right_splits_closedSegment_of_succDegree hf_pos hg_pos hfg hsucc

/-- Challenge-facing lower-degree endpoint packaged as `≠ 0 ∧ Splits`. -/
theorem succDegreeLeftEndpointNeZeroAndSplits {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f ≠ 0 ∧ f.Splits :=
  RealRooted.left_ne_zero_and_splits_closedSegment_of_succDegree
    hf_pos hg_pos hfg hsucc

/-- Challenge-facing higher-degree endpoint packaged as `≠ 0 ∧ Splits`. -/
theorem succDegreeRightEndpointNeZeroAndSplits {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g ≠ 0 ∧ g.Splits :=
  RealRooted.right_ne_zero_and_splits_closedSegment_of_succDegree
    hf_pos hg_pos hfg hsucc

/-- Challenge-facing lower-degree endpoint root-card package. -/
theorem succDegreeLeftEndpointCardRoots {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.roots.card = f.natDegree :=
  RealRooted.left_card_roots_of_succDegree hf_pos hg_pos hfg hsucc

/-- Challenge-facing higher-degree endpoint root-card package. -/
theorem succDegreeRightEndpointCardRoots {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.roots.card = g.natDegree :=
  RealRooted.right_card_roots_of_succDegree hf_pos hg_pos hfg hsucc

/-- Challenge-facing inclusive closed-segment lower-degree endpoint. -/
theorem succDegreeLeftEndpointClosedSegmentIccSplits {f g : ℝ[X]}
    (hfamily : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits))
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.Splits :=
  RealRooted.splits_of_closedSegmentIcc_family_of_succDegree
    hfamily hf_pos hg_pos hsucc

/-- Challenge-facing inclusive closed-segment higher-degree endpoint. -/
theorem succDegreeRightEndpointClosedSegmentIccSplits {f g : ℝ[X]}
    (hfamily : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits))
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.Splits :=
  RealRooted.splits_right_of_closedSegmentIcc_family_of_succDegree
    hfamily hf_pos hg_pos hsucc

/-- Challenge-facing `Prec`-level degree-drop for the right-zero lead branch. -/
theorem succDegreePrecDivXLeftOfPrec {f g : ℝ[X]}
    (hprec : Prec f g) (hgnn : HasNonnegCoeffs g) (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec (g.divX) f :=
  RealRooted.prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero
    hprec hgnn hg0 hdeg

/-- Challenge-facing converse right-zero degree-drop reconstruction. -/
theorem succDegreePrecOfPrecDivXLeft {f g : ℝ[X]}
    (hprec : Prec (g.divX) f) (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec f g :=
  RealRooted.prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero
    hprec hfnn hgnn hg0 hdeg

/-- Challenge-facing right-zero degree-drop equivalence. -/
theorem succDegreePrecIffPrecDivXLeft {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec f g ↔ Prec (g.divX) f :=
  RealRooted.prec_iff_prec_divX_left_of_hasNonnegCoeffs_coeff_zero
    hfnn hgnn hg0 hdeg

/-- Challenge-facing `Prec0`-level degree-drop for the right-zero lead branch. -/
theorem succDegreePrec0DivXLeftOfPrec {f g : ℝ[X]}
    (hprec : Prec f g) (hgnn : HasNonnegCoeffs g) (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec0 (g.divX) f :=
  RealRooted.prec0_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero
    hprec hgnn hg0 hdeg

/-- Challenge-facing reflected-family splitting equivalence. -/
theorem reflectedFamilySplitsIff {a b : ℝ} {f g : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits ↔
      (C a * f + C b * g).Splits :=
  RealRooted.DegreeDropReversal.splits_reflected_family_iff hfN hgN

/-- Challenge-facing reverse/divX additive family splitting equivalence. -/
theorem reverseFamilySplitsIffDivXAdd {a b : ℝ} {f g : ℝ[X]}
    (h0 : (C a * f + C b * g).coeff 0 = 0) :
    (C a * f + C b * g).reverse.Splits ↔
      (C a * f.divX + C b * g.divX).Splits :=
  RealRooted.DegreeDropReversal.splits_reverse_family_iff_divX_add_of_coeff_zero h0

/-- Challenge-facing reflected/divX additive family splitting equivalence. -/
theorem reflectedFamilySplitsIffDivXAdd {a b : ℝ} {f g : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N)
    (h0 : (C a * f + C b * g).coeff 0 = 0) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits ↔
      (C a * f.divX + C b * g.divX).Splits :=
  RealRooted.DegreeDropReversal.splits_reflected_family_iff_divX_add_of_coeff_zero
    hfN hgN h0

/-- Challenge-facing lower-threshold root-count gap stability from common non-roots. -/
theorem rootCountDiffLeOneOfNonRoot {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 :=
  RealRooted.rootCount_diff_le_one_of_nonRoot hf hg hbound

/-- Challenge-facing absolute-value form of lower-threshold root-count stability. -/
theorem rootCountAbsDiffLeOneOfNonRoot {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 :=
  RealRooted.rootCount_abs_diff_le_one_of_nonRoot hf hg hbound

/-- Challenge-facing max-form projection from bundled lower/upper root-count gaps. -/
theorem rootCountMaxAbsDiffLeOneOfBundled {f g : ℝ[X]}
    (h : ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 ∧
      |((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card| ≤ 1) :
    ∀ x : ℝ,
      max
        |((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card|
        |((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card|
          ≤ 1 :=
  RealRooted.rootCount_max_abs_diff_le_one_of_bundled h

/-- Challenge-facing lower-threshold bound transport across a root-free window. -/
theorem cardRootsFilterLeBoundOfNoIsRootIoc {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (h : ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ a)).card : ℤ) - (f.roots.filter (· ≤ a)).card ≤ 1) :
    ((f.roots.filter (· ≤ b)).card : ℤ) - (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) - (f.roots.filter (· ≤ b)).card ≤ 1 :=
  RealRooted.card_roots_filter_le_bound_of_no_isRoot_Ioc hab hf hg h

/-- Challenge-facing upper-threshold bound transport across a root-free window. -/
theorem cardRootsFilterGtBoundOfNoIsRootIoc {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (h : ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card ≤ 1 ∧
      ((g.roots.filter (a < ·)).card : ℤ) - (f.roots.filter (a < ·)).card ≤ 1) :
    ((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card ≤ 1 ∧
      ((g.roots.filter (b < ·)).card : ℤ) - (f.roots.filter (b < ·)).card ≤ 1 :=
  RealRooted.card_roots_filter_gt_bound_of_no_isRoot_Ioc hab hf hg h

end ChudnovskySeymour
end Challenges
end RealRooted
