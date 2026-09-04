import RealRooted.ChudnovskySeymour.Core

/-!
# Chudnovsky--Seymour endpoint adapters

This umbrella extends the proved pair/family core with roadmap reductions,
direct endpoint combinations, and low-degree wrappers. Clients needing only
the proved core theorem surface should import
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

/-! ### Same-degree endpoints combined with the direct #42 closed-segment /
endpoint-sign lower-count succ-degree route

These core wrappers are the non-challenge analogues of the composition wrappers
in `Challenges/ChudnovskySeymour.lean`: they feed a same-degree no-common
endpoint (the repaired pair endpoint, or its slot-data, root-crossing, and lower
root-count leaves) together with the direct #42-compatible succ-degree
closed-segment endpoint count-equality or endpoint-sign lower-count leaf into
the nonnegative finite-family targets, so downstream users do not have to route
through the challenge file.  All are pure term-mode wrappers over existing
reductions and introduce no new mathematical assumptions.  The same-degree
common-non-root root-count leaf already has these wrappers above; here we cover
the repaired pair endpoint and its slot-data / root-crossing / lower root-count
reductions. -/

/-- Nonnegative four-way package target from the repaired same-degree pair
endpoint and the #42 compatible succ-degree closed-segment endpoint count
equality. -/
theorem chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg hsame
    (succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq hsucc)

/-- Nonnegative-coefficient common-interleaver target from the repaired
same-degree pair endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg hsame
    (succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq hsucc)

/-- Nonnegative-coefficient finite-family compatibility target from the
repaired same-degree pair endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_nonneg hsame
    (succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq hsucc)

/-- Nonnegative four-way package target from the repaired same-degree pair
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    hsame (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-- Nonnegative-coefficient common-interleaver target from the repaired
same-degree pair endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg hsame
    (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-- Nonnegative-coefficient finite-family compatibility target from the
repaired same-degree pair endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg hsame
    (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-! #### Same-degree slot-data endpoint with the direct #42 route

The same-degree slot-data endpoint feeds the repaired same-degree pair endpoint
through `sameDegreePairHasCommonInterleaver_nonneg_of_slotData`. -/

/-- Nonnegative four-way package target from the same-degree slot-data endpoint
and the #42 compatible succ-degree closed-segment endpoint count equality. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeSlotData_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
slot-data endpoint and the #42 compatible succ-degree closed-segment endpoint
count equality. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeSlotData_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree slot-data endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeSlotData_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative four-way package target from the same-degree slot-data endpoint
and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeSlotData_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
slot-data endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeSlotData_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree slot-data endpoint and the #42 exact lower-threshold endpoint-sign
count equality leaf. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeSlotData_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-! #### Same-degree root-crossing endpoint with the direct #42 route

The same-degree root-crossing endpoint feeds the repaired same-degree pair
endpoint through `sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing`. -/

/-- Nonnegative four-way package target from the same-degree root-crossing
endpoint and the #42 compatible succ-degree closed-segment endpoint count
equality. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
root-crossing endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_succClosedSegmentEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree root-crossing endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative four-way package target from the same-degree root-crossing
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
root-crossing endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree root-crossing endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-! #### Same-degree lower root-count endpoint with the direct #42 route

The same-degree lower-threshold root-count endpoint feeds the repaired
same-degree pair endpoint through
`sameDegreePairHasCommonInterleaver_nonneg_of_rootCount`. -/

/-- Nonnegative four-way package target from the same-degree lower root-count
endpoint and the #42 compatible succ-degree closed-segment endpoint count
equality. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCount_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree lower
root-count endpoint and the #42 compatible succ-degree closed-segment endpoint
count equality. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeRootCount_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree lower root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeRootCount_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative four-way package target from the same-degree lower root-count
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCount_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree lower
root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeRC_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree lower root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeRC_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-! #### Same-degree upper root-count endpoint with the direct #42 route

The same-degree upper-threshold root-count endpoint feeds the repaired
same-degree pair endpoint through
`sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove`. -/

/-- Nonnegative four-way package target from the same-degree upper root-count
endpoint and the #42 compatible succ-degree closed-segment endpoint count
equality. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeRootCountAbove_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree upper
root-count endpoint and the #42 compatible succ-degree closed-segment endpoint
count equality. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeRootCountAbove_and_succClosedSegmentEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree upper root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeRCAbove_and_succClosedSegmentEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative four-way package target from the same-degree upper root-count
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeRootCountAbove_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree upper
root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeRCAbove_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree upper root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeRCAbove_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-! #### Same-degree common-non-root upper root-count endpoint with the direct
#42 route

The same-degree common-non-root upper-threshold root-count endpoint feeds the
repaired same-degree pair endpoint through
`sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot`. -/

/-- Nonnegative four-way package target from the same-degree common-non-root
upper root-count endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeRootCountAboveNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root upper root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_commonInterleaver_of_rootCountAboveNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root upper root-count endpoint and the #42 compatible
succ-degree closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_rootCountAboveNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative four-way package target from the same-degree common-non-root
upper root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_fourWay_of_rootCountAboveNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root upper root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_rootCountAboveNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root upper root-count endpoint and the #42 exact
lower-threshold endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_familyCompatible_of_rootCountAboveNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-! #### Same-degree common-non-root lower root-count endpoint with the direct
#42 route

The same-degree common-non-root lower-threshold root-count endpoint feeds the
repaired same-degree pair endpoint through
`sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot`. -/

/-- Nonnegative four-way package target from the same-degree common-non-root
lower root-count endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root lower root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_commonInterleaver_of_rootCountNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root lower root-count endpoint and the #42 compatible
succ-degree closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_rootCountNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative four-way package target from the same-degree common-non-root
lower root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeRootCountNonRoot_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root lower root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_rootCountNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root lower root-count endpoint and the #42 exact
lower-threshold endpoint-sign count equality leaf. -/
theorem
    chudnovskySeymour_familyCompatible_of_rootCountNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Degree-`≤ 1` positive-leading families already satisfy the common-interleaver
form of Chudnovsky--Seymour without the two-polynomial bridge hypothesis. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one hpos hdeg

/-- Degree-`≤ 1` positive-leading families also satisfy the left-oriented
common-interleaver form of Chudnovsky--Seymour without the two-polynomial
bridge hypothesis. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  pairwiseCompatible_iff_commonLeftInterleaver_of_natDegree_le_one hpos hdeg

/-- Degree-`≤ 1` positive-leading families also satisfy the full-family
compatibility form of Chudnovsky--Seymour without the two-polynomial bridge
hypothesis. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one hpos hdeg

end RealRooted
