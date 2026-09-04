import RealRooted.ChudnovskySeymour.Core

/-!
# Chudnovsky--Seymour roadmap reductions

This module extends the proved pair/family core with generic roadmap reductions
and their first direct successor-degree adapters. Clients needing only the
proved core theorem surface should import
`RealRooted.ChudnovskySeymour.Core`.
-/

noncomputable section

namespace RealRooted

open Polynomial

/-- The nonnegative four-way package target follows from the honest same-degree
orientation alternative and successor-degree bridge. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_degreeSplit_and_nonnegCoeffs
      hrr hpos hnn hsame hsucc

/-- The nonnegative-coefficient roadmap target follows from the honest
same-degree orientation alternative and successor-degree bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_degreeSplit_nonneg hsame hsucc)

/-- The nonnegative four-way package target follows from the repaired
same-degree bridge and the affine-family bridge for the successor-degree
branch. -/
theorem chudnovskySeymour_fourWayTarget_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
      hrr hpos hnn hsame haffBridge

/-- The nonnegative-coefficient common-interleaver target follows from the
repaired same-degree bridge and the affine-family bridge for the
successor-degree branch. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreePair_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWayTarget_of_sameDegreePair_and_affineFamily_nonneg
      hsame haffBridge)

/-- The nonnegative four-way package target follows from the all-combinations
bridge. -/
theorem chudnovskySeymour_fourWay_of_allComboBridge_nonneg
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs
      hrr hpos hnn hallBridge

/-- The nonnegative-coefficient common-interleaver target follows from the
all-combinations bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_allComboBridge_nonneg
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_allComboBridge_nonneg hallBridge)

/-- The nonnegative four-way package target follows from the affine-family
bridge. -/
theorem chudnovskySeymour_fourWay_of_affineFamilyBridge_nonneg
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
      hrr hpos hnn haffBridge

/-- The nonnegative-coefficient common-interleaver target follows from the
affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_affineFamilyBridge_nonneg
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_affineFamilyBridge_nonneg haffBridge)

/-- The nonnegative four-way package target follows from the
boundary-right-pair orientation statement. -/
theorem chudnovskySeymour_fourWay_of_boundaryRight_nonneg
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_and_nonnegCoeffs
      hrr hpos hnn hboundary

/-- The nonnegative-coefficient roadmap target follows from the
boundary-right-pair orientation statement. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_boundaryRight_nonneg hboundary)

/-- The nonnegative-coefficient finite-family compatibility target is a formal
consequence of the corresponding common-interleaver target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (hcommon : chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos
      (hcommon hrr hpos hnn).1

/-- The nonnegative-coefficient finite-family compatibility target follows
from the no-common orientation core. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_noCommonOrientation_nonneg
    (hstep : PosComboNoCommonOrientationStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_noCommonOrientation_nonneg
      hstep)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the repaired same-degree and successor-degree no-common pair bridges. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
      hsame hsucc)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the honest same-degree orientation alternative and successor-degree
bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_degreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
      hsame hsucc)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the repaired same-degree bridge and the affine-family bridge for the
successor-degree branch. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreePair_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_commonInterleaver_of_sameDegreePair_affineFamily_nonneg
      hsame haffBridge)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the all-combinations bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_allComboBridge_nonneg
    (hallBridge : PosComboNoCommonToAllComboBridgeStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_allComboBridge_nonneg
      hallBridge)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_nonneg
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_affineFamilyBridge_nonneg
      haffBridge)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the boundary-right-pair orientation statement. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_boundaryRight_nonneg
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
      hboundary)

/-- The nonnegative four-way package target follows from the same-degree
common-non-root root-count leaf and the direct compatible succ-degree
closed-segment endpoint count-equality route. -/
theorem
    chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCountAboveNonRoot_nonneg hsame
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hsucc)

/-- The nonnegative-coefficient common-interleaver target follows from the
same-degree common-non-root root-count leaf and the direct compatible
succ-degree closed-segment endpoint count-equality route. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
      hsame hsucc)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the same-degree common-non-root root-count leaf and the direct compatible
succ-degree closed-segment endpoint count-equality route. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
      hsame hsucc)

/-- The nonnegative four-way package target also follows from the same-degree
common-non-root root-count leaf and the exact lower-threshold endpoint-sign
count-equality form of the direct compatible succ-degree route. -/
theorem
    chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    hsame (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-- The nonnegative-coefficient common-interleaver target follows from the
same-degree common-non-root root-count leaf and the exact lower-threshold
endpoint-sign count-equality form of the direct compatible succ-degree route. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameRootCountNonRoot_and_succLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succEndpointSignLowerCountEq_nonneg
      hsame hsucc)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the same-degree common-non-root root-count leaf and the exact
lower-threshold endpoint-sign count-equality form of the direct compatible
succ-degree route. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameRootCountNonRoot_and_succLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succEndpointSignLowerCountEq_nonneg
      hsame hsucc)

end RealRooted
