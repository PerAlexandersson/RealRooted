import RealRooted.CommonInterleaverTwo

noncomputable section

namespace RealRooted

open Polynomial

/--
Roadmap stub for the full Chudnovsky–Seymour compatibility direction.

This file is intentionally a placeholder for the remaining global theorem:
pairwise compatibility should be equivalent to common interleaver data under
the usual real-rooted/splits and positivity hypotheses.
-/
def chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_statement

/-- Legacy reduction of the common-left roadmap target from the two inputs used
before the finite-family left Helly upgrade was internalized.
-/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal : CommonLeftInterleaverFamilyUpgradeStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target :=
  fun {fs} hrr hpos =>
    pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
      (fs := fs) hpos htwo (hglobal (fun f hf => (hrr f hf).2) hpos)

/-- Direct roadmap wrapper after the finite-family common-left upgrade: the
common-left Chudnovsky--Seymour target now only needs the two-polynomial
common-left bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target :=
  fun {fs} hrr hpos =>
    pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
      (fs := fs) (fun f hf => (hrr f hf).2) hpos htwo

/--
Roadmap target for a direct pairwise-to-common interleaver equivalence.

This has not been fully formalized in the project yet and is listed in the
current issue plan as a next substantive step.
-/
def chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (PairwiseCompatible fs ↔ HasCommonInterleaver fs)

/--
Roadmap target for the full finite-family compatibility equivalence.

This is the `1 ↔ 4` Chudnovsky--Seymour surface under the same standard
real-rooted/splits and positive-leading hypotheses as
`chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target`.
-/
def chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (PairwiseCompatible fs ↔ FamilyCompatible fs)

/--
Roadmap target for the nonnegative-coefficient form of the direct
pairwise-to-common interleaver equivalence.

This is the theorem surface most directly connected to the current
same-degree/succ-degree endpoint work.
-/
def chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :
    Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (∀ f ∈ fs, HasNonnegCoeffs f) →
    (PairwiseCompatible fs ↔ HasCommonInterleaver fs)

/--
Roadmap target for the nonnegative-coefficient form of the finite-family
compatibility equivalence.

This packages the `1 ↔ 4` Chudnovsky--Seymour surface in the same
nonnegative-coefficient regime as
`chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target`.
-/
def chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :
    Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (∀ f ∈ fs, HasNonnegCoeffs f) →
    (PairwiseCompatible fs ↔ FamilyCompatible fs)

/--
Roadmap target for the nonnegative-coefficient four-way
Chudnovsky--Seymour package.

This is the strongest finite-family target currently exposed in the
nonnegative-coefficient regime; the common-interleaver and family-compatible
targets are projections from it.
-/
def chudnovskySeymour_fourWay_nonnegCoeffs_target : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (∀ f ∈ fs, HasNonnegCoeffs f) →
    ChudnovskySeymourFourWayPackage fs

/-- The roadmap target follows from the natural positive-leading two-polynomial
bridge used by the finite-family machinery. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos hrr hpos htwo

/-- The finite-family compatibility roadmap target is a formal consequence of
the corresponding common-interleaver target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (hcommon : chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_forward hpos
      (hcommon hrr hpos).1

/-- The finite-family compatibility roadmap target follows from the natural
positive-leading two-polynomial bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge htwo)

/-- The roadmap target follows from the same-degree and successor-degree
two-polynomial bridges. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_compatibleDegreeSplit
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from the
same-degree and successor-degree two-polynomial bridges. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_degreeSplit
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit
      hsame hsucc)

/-- The roadmap target follows from the nonnegative-shift route, with the
succ-degree branch discharged by the affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
      hrr hpos hsame haffBridge

/-- The finite-family compatibility roadmap target follows from the
nonnegative-shift route, with the succ-degree branch discharged by the
affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_nonnegShift
      hsame haffBridge)

/-- The roadmap target follows from the concrete slot-data endpoints after the
nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_slotData
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from the concrete
slot-data endpoints after the nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_slotData
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_slotData
      hsame hsucc)

/-- The roadmap target follows from the root-crossing formulations of the
same-degree and succ-degree endpoints after the nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
      hrr hpos hsame hsplit hsucc

/-- The finite-family compatibility roadmap target follows from the
root-crossing formulations after the nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsplit : PosComboSuccDegreeLeftSplitsNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing
      hsame hsplit hsucc)

/-- The roadmap target follows from the root-crossing formulations alone:
root continuity supplies the succ-degree left endpoint. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_direct
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from root-crossing
alone; root continuity supplies the succ-degree left endpoint. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing_direct
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_direct
      hsame hsucc)

/-- The roadmap target follows from the root-crossing formulations once the
succ-degree left endpoint is supplied by the PF/ASW route. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forward_asw
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
      hrr hpos hsame hASW hsucc

/-- The finite-family compatibility roadmap target follows from root-crossing
once the succ-degree left endpoint is supplied by the PF/ASW route. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forward_asw
      hsame hASW hsucc)

/-- The roadmap target follows from the root-crossing formulations once the
succ-degree left endpoint is supplied by the splitting-only ASW target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forwardASWSplits
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw_splits
      hrr hpos hsame hASW hsucc

/-- The finite-family compatibility roadmap target follows from root-crossing
once the succ-degree left endpoint is supplied by the splitting-only ASW
target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forwardASWSplits
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forwardASWSplits
      hsame hASW hsucc)

/-- The roadmap target also follows from the same-degree root-crossing
formulation and the affine-family bridge, avoiding the separate succ-degree
root-crossing branch. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeCrossing_affineFamily
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge
    (compatiblePairHasCommonInterleaver_of_sameDegreePair_and_affineFamily_via_nonnegShift
      (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame)
      haffBridge)

/-- The finite-family compatibility roadmap target follows from same-degree
root-crossing and the affine-family bridge. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeCrossing_affineFamily
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_commonInterleaver_of_sameDegreeCrossing_affineFamily
      hsame haffBridge)

/-- The nonnegative four-way package target follows from the root-crossing
formulations once the succ-degree left endpoint is supplied by the
splitting-only ASW target. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos _ =>
    chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw_splits
      hrr hpos hsame hASW hsucc

/-- The nonnegative four-way package target follows from the root-crossing
formulations alone; root continuity supplies the succ-degree left endpoint. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos _ =>
    RealRooted.chudnovskySeymour_fourWay_of_rootCrossing
      hrr hpos hsame hsucc

/-- The nonnegative four-way package target follows from lower-threshold
root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCount_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- The nonnegative four-way package target follows from same-degree
lower-threshold root counts and succ-degree upper-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_rootCountAbove_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- The nonnegative four-way package target follows from same-degree
upper-threshold root counts and succ-degree lower-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_sameRootCountAbove_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- The nonnegative four-way package target follows from upper-threshold
root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCountAboveBoth_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- The nonnegative four-way package target follows from common-non-root
lower-threshold root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCountNonRoot_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- The nonnegative four-way package target follows from same-degree
common-non-root lower-threshold root counts and succ-degree common-non-root
upper-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_rootCountAboveNonRoot_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- The nonnegative four-way package target follows from same-degree
common-non-root upper-threshold root counts and succ-degree common-non-root
lower-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_sameRootCountAboveNonRoot_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- The nonnegative four-way package target follows from common-non-root
upper-threshold root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCountAboveBothNonRoot_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- The nonnegative four-way package target follows from same-degree
root-crossing and the affine-family bridge for the succ-degree branch. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
      hrr hpos hnn
      (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame)
      haffBridge

/-- The nonnegative common-interleaver target follows from the root-crossing
formulations and splitting-only ASW. -/
theorem
    chudnovskySeymour_commonInterleaver_of_rootCrossing_forwardASWSplits_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
        hsame hASW hsucc hrr hpos hnn)

/-- The nonnegative common-interleaver target follows from the root-crossing
formulations alone. -/
theorem chudnovskySeymour_commonInterleaver_of_rootCrossing_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_nonneg
        hsame hsucc hrr hpos hnn)

/-- The nonnegative common-interleaver target follows from same-degree
root-crossing and the affine-family bridge. -/
theorem chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
      (chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_affineFamily_nonneg
        hsame haffBridge hrr hpos hnn)

/-- The nonnegative finite-family compatibility target follows from the
root-crossing formulations and splitting-only ASW. -/
theorem
    chudnovskySeymour_familyCompatible_of_rootCrossing_forwardASWSplits_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hASW : aissenSchoenbergWhitneyForwardSplitsStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
        hsame hASW hsucc hrr hpos hnn)

/-- The nonnegative finite-family compatibility target follows from the
root-crossing formulations alone. -/
theorem chudnovskySeymour_familyCompatible_of_rootCrossing_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCrossingNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_nonneg
        hsame hsucc hrr hpos hnn)

/-- The nonnegative finite-family compatibility target follows from
same-degree root-crossing and the affine-family bridge. -/
theorem chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCrossingNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_fourWay
      (chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_affineFamily_nonneg
        hsame haffBridge hrr hpos hnn)

/-- The nonnegative-coefficient common-interleaver target is a projection of
the nonnegative four-way package target. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (hfour : chudnovskySeymour_fourWay_nonnegCoeffs_target) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay (hfour hrr hpos hnn)

/-- The nonnegative-coefficient finite-family compatibility target is a
projection of the nonnegative four-way package target. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_fourWay_nonneg
    (hfour : chudnovskySeymour_fourWay_nonnegCoeffs_target) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_fourWay (hfour hrr hpos hnn)

/-- The nonnegative four-way package target follows from the no-common
orientation core. -/
theorem chudnovskySeymour_fourWay_of_noCommonOrientation_nonneg
    (hstep : PosComboNoCommonOrientationStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
      hrr hpos hnn hstep

/-- The nonnegative-coefficient common-interleaver target follows from the
no-common orientation core. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_noCommonOrientation_nonneg
    (hstep : PosComboNoCommonOrientationStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_noCommonOrientation_nonneg hstep)

/-- The nonnegative four-way package target follows from the repaired
same-degree and successor-degree no-common pair bridges. -/
theorem chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
      hrr hpos hnn hsame hsucc

/-- The nonnegative-coefficient roadmap target follows from the repaired
same-degree and successor-degree no-common pair bridges. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg hsame hsucc)

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
  chudnovskySeymour_commonInterleaver_of_sameDegreeSlotData_and_succEndpointSignLowerCountEq_nonneg
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
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_succClosedSegmentCountEq_nonneg
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
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCount_and_succEndpointSignLowerCountEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree lower root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCount_and_succEndpointSignLowerCountEq_nonneg
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
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCountAbove_and_succClosedSegmentCountEq_nonneg
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
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCountAbove_and_succEndpointSignLowerEq_nonneg
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonnegStatement)
    (hsucc : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree upper root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCountAbove_and_succEndpointSignLowerEq_nonneg
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
