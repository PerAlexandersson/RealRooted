import RealRooted.ClosedSegmentCountEqFromAnalytic
import RealRooted.CommonInterleaverTwo
import RealRooted.InterlacingSequenceBasic
import RealRooted.SameDegreeCountFromAnalytic

noncomputable section

namespace RealRooted

open Polynomial

/-- Chudnovsky--Seymour for two polynomials: compatible polynomials with positive
leading coefficients have a common (right) interleaver.  The proof splits into
the same-degree and successor-degree cases. -/
theorem chudnovskySeymour_compatiblePairHasCommonInterleaver :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonneg
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonneg

/-- Chudnovsky--Seymour for two polynomials, common-left form: compatible
polynomials with positive leading coefficients have a common left interleaver. -/
theorem chudnovskySeymour_compatiblePairHasCommonLeftInterleaver :
    CompatiblePairHasCommonLeftInterleaverPosStatement :=
  compatiblePairHasCommonLeftInterleaverPos_of_pairBridge
    chudnovskySeymour_compatiblePairHasCommonInterleaver

/-- Two compatible polynomials with positive leading coefficients have a common
interleaver. -/
theorem compatiblePairHasCommonInterleaver_chudnovskySeymour
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : Compatible f g) :
    ∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl g k :=
  chudnovskySeymour_compatiblePairHasCommonInterleaver hf hg h

/-- Two compatible polynomials with positive leading coefficients have a common
left interleaver. -/
theorem compatiblePairHasCommonLeftInterleaver_chudnovskySeymour
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : Compatible f g) :
    ∃ k : ℝ[X], StrictInterl k f ∧ StrictInterl k g :=
  chudnovskySeymour_compatiblePairHasCommonLeftInterleaver hf hg h

/-- **Chudnovsky--Seymour.** A finite family of real-rooted polynomials with
positive leading coefficients is pairwise compatible if and only if it has a
common interleaver. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos hrr hpos
    (fun _ _ hf hg h => compatiblePairHasCommonInterleaver_chudnovskySeymour hf hg h)

/-- **Chudnovsky--Seymour**, common-left form: a finite family of real-rooted
polynomials with positive leading coefficients is pairwise compatible if and
only if it has a common left interleaver. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    chudnovskySeymour_compatiblePairHasCommonLeftInterleaver
    (fun f hf => (hrr f hf).2) hpos

/-- **Chudnovsky--Seymour.** A finite family of real-rooted polynomials with
positive leading coefficients is pairwise compatible if and only if every
nonnegative combination of its members is zero or real-rooted. -/
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

/-- The four equivalent Chudnovsky--Seymour conditions for a family with
nonnegative coefficients: pairwise compatibility, pairwise and common
interleavers, and family compatibility. -/
theorem chudnovskySeymour_fourWay_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs hrr hpos hnn
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonneg
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonneg

/-- `chudnovskySeymour_pairwiseCompatible_iff_familyCompatible` with an unused
nonnegativity hypothesis, kept for existing callers. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (_hnn : ∀ f ∈ fs, HasNonnegCoeffs f) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible hrr hpos

end RealRooted
