import RealRooted.ClosedSegmentCountEqFromAnalytic
import RealRooted.CommonInterleaverTwo
import RealRooted.InterlacingSequenceBasic
import RealRooted.SameDegreeCountFromAnalytic

noncomputable section

namespace RealRooted

open Polynomial

/-- Checked positive-leading two-polynomial Chudnovsky--Seymour common-right
bridge assembled from the same-degree and successor-degree analytic endpoints.
-/
theorem chudnovskySeymour_compatiblePairHasCommonInterleaver :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonneg
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonneg

/-- Checked positive-leading two-polynomial Chudnovsky--Seymour common-left
bridge, derived from the common-right bridge by the existing left/right
conversion.
-/
theorem chudnovskySeymour_compatiblePairHasCommonLeftInterleaver :
    CompatiblePairHasCommonLeftInterleaverPosStatement :=
  compatiblePairHasCommonLeftInterleaverPos_of_pairBridge
    chudnovskySeymour_compatiblePairHasCommonInterleaver

/-- Pair-level common-right interleaver form of the checked
Chudnovsky--Seymour bridge. -/
theorem compatiblePairHasCommonInterleaver_chudnovskySeymour
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : Compatible f g) :
    ∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl g k :=
  chudnovskySeymour_compatiblePairHasCommonInterleaver hf hg h

/-- Pair-level common-left interleaver form of the checked
Chudnovsky--Seymour bridge. -/
theorem compatiblePairHasCommonLeftInterleaver_chudnovskySeymour
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : Compatible f g) :
    ∃ k : ℝ[X], StrictInterl k f ∧ StrictInterl k g :=
  chudnovskySeymour_compatiblePairHasCommonLeftInterleaver hf hg h

/--
Roadmap stub for the full Chudnovsky–Seymour compatibility direction.

This file is intentionally a placeholder for the remaining global theorem:
pairwise compatibility should be equivalent to common interleaver data under
the usual real-rooted/splits and positivity hypotheses.
-/
def chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_statement

/-- The common-left roadmap target follows from the positive-leading common
right two-polynomial bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairBridge
    (hright : CompatiblePairHasCommonInterleaverStatement) :
    chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target :=
  fun {fs} hrr hpos =>
    pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridgePos_direct
      (fs := fs) (fun f hf => (hrr f hf).2) hpos
      (compatiblePairHasCommonLeftInterleaverPos_of_pairBridge hright)

/-- The proved #41 same-degree endpoint and #42 successor-degree endpoint close
the left-oriented pairwise/common-left-interleaver Chudnovsky--Seymour target.
-/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver :
    chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairBridge
    chudnovskySeymour_compatiblePairHasCommonInterleaver

/--
Pairwise compatibility is equivalent to a common interleaver for the whole
family.  This statement is proved, without hypotheses, by
`chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge`.
-/
def chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits)) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    (PairwiseCompatible fs ↔ HasCommonInterleaver fs)

/-- Chudnovsky--Seymour pairwise-to-family compatibility equivalence.

This is the `1 ↔ 4` Chudnovsky--Seymour surface under the same standard
real-rooted/splits and positive-leading hypotheses as
`chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target`. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_pairBridgePos hrr hpos
    chudnovskySeymour_compatiblePairHasCommonInterleaver

/-- An interlacing sequence with nonnegative coefficients is compatible under
all nonnegative weighted sums. -/
theorem IsInterlacingSeqNonneg.familyCompatible
    {fs : List ℝ[X]} (hfs : IsInterlacingSeqNonneg fs) :
    FamilyCompatible fs := by
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := fun f hf ↦ (hfs.1 f hf).1
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f :=
    fun f hf => (hfs.1 f hf).2.pos_leadingCoeff (hfs.1 f hf).1.1
  apply (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible hrr hpos).mp
  have hstrictInterl := isInterlacingSeq_iff_pairwise.mp hfs.2
  rw [List.pairwise_iff_get] at hstrictInterl
  intro i j hij
  exact Compatible.of_strictInterl (hstrictInterl i j hij)

/-- Every nonnegative weighted sum drawn from a nonnegative interlacing
sequence is a Pólya-frequency polynomial. -/
theorem IsInterlacingSeqNonneg.weightedSum_isPFPolynomial
    {fs : List ℝ[X]} (hfs : IsInterlacingSeqNonneg fs)
    (ws : List (ℝ × ℝ[X]))
    (hmem : ∀ ap ∈ ws, ap.2 ∈ fs)
    (hweights : ∀ ap ∈ ws, 0 ≤ ap.1) :
    IsPFPolynomial (weightedSum ws) := by
  have hnonneg : HasNonnegCoeffs (weightedSum ws) :=
    hasNonnegCoeffs_weightedSum ws hweights fun ap hap ↦
      (hfs.1 ap.2 (hmem ap hap)).2
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnonneg <|
    (hfs.familyCompatible ws hmem hweights).imp_right And.right

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
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos hrr hpos
      (fun _ _ hf hg h =>
        compatiblePairHasCommonInterleaver_chudnovskySeymour hf hg h)

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

/-- The proved #41 same-degree endpoint and #42 successor-degree endpoint close
the nonnegative-coefficient four-way Chudnovsky--Seymour package. -/
theorem chudnovskySeymour_fourWay_nonnegCoeffs :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonneg
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonneg

/-- The nonnegative-coefficient finite-family compatibility form follows from
the proved #41/#42 endpoint package. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_fourWay_nonneg
    chudnovskySeymour_fourWay_nonnegCoeffs


end RealRooted
