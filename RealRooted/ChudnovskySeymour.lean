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

/-- The roadmap target follows from the natural positive-leading two-polynomial
bridge used by the finite-family machinery. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos hrr hpos htwo

/-- The roadmap target follows from the same-degree and successor-degree
two-polynomial bridges. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit
    (hsame : CompatibleSameDegreePairHasCommonInterleaverStatement)
    (hsucc : CompatibleSuccDegreePairHasCommonInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_compatibleDegreeSplit
      hrr hpos hsame hsucc

/-- The roadmap target follows from the nonnegative-shift route, with the
succ-degree branch discharged by the affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_nonnegShift
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (haffBridge : PosComboNoCommonAffineFamilyStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
      hrr hpos hsame haffBridge

/-- The roadmap target follows from the concrete slot-data endpoints after the
nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_slotData
    (hsame : PosComboNoCommonSameDegreeSlotDataNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeSlotDataNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
      hrr hpos hsame hsucc

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

/-- The nonnegative-coefficient roadmap target follows from the repaired
same-degree and successor-degree no-common pair bridges. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_pairDegreeSplit_and_nonnegCoeffs
      hrr hpos hnn hsame hsucc

/-- The nonnegative-coefficient roadmap target follows from the honest
same-degree orientation alternative and successor-degree bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_degreeSplit_and_nonnegCoeffs
      hrr hpos hnn hsame hsucc

/-- The nonnegative-coefficient roadmap target follows from the
boundary-right-pair orientation statement. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_boundaryRightPairOrientation_and_nonnegCoeffs
      hrr hpos hnn hboundary

/-- The nonnegative-coefficient finite-family compatibility target is a formal
consequence of the corresponding common-interleaver target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (hcommon : chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    ⟨fun hpair =>
      familyCompatible_of_commonInterleaver ((hcommon hrr hpos hnn).1 hpair) hpos,
      pairwiseCompatible_of_familyCompatible⟩

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
from the boundary-right-pair orientation statement. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_boundaryRight_nonneg
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
      hboundary)

/-- Degree-`≤ 1` positive-leading families already satisfy the common-interleaver
form of Chudnovsky--Seymour without the two-polynomial bridge hypothesis. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one hpos hdeg

end RealRooted
