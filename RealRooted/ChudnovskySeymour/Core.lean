import RealRooted.CommonInterleaverTwo
import RealRooted.InterlacingSequenceBasic
import RealRooted.SameDegreeCountFromAnalytic

noncomputable section

namespace RealRooted

open Polynomial

/-- Implicit-binder form of `chudnovskySeymour_compatiblePairHasCommonInterleaver`,
kept for existing callers. -/
theorem compatiblePairHasCommonInterleaver_chudnovskySeymour
    {f g : ℝ[X]} (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : Compatible f g) :
    ∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl g k :=
  chudnovskySeymour_compatiblePairHasCommonInterleaver hf hg h

/-- **Chudnovsky--Seymour for two polynomials**, common-left form: compatible
polynomials with positive leading coefficients have a common left interleaver.
A common right interleaver is converted using degree closeness. -/
theorem chudnovskySeymour_compatiblePairHasCommonLeftInterleaver
    ⦃f g : ℝ[X]⦄ (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : Compatible f g) :
    ∃ k : ℝ[X], StrictInterl k f ∧ StrictInterl k g := by
  have hclose : f.natDegree ≤ g.natDegree + 1 ∧ g.natDegree ≤ f.natDegree + 1 :=
    h.natDegree_close hf hg
  by_cases hdeg : f.natDegree ≤ g.natDegree
  · obtain ⟨k, hfk, hgk⟩ := chudnovskySeymour_compatiblePairHasCommonInterleaver hf hg h
    exact pairHasCommonLeftInterleaver_of_commonInterleaver hfk hgk hdeg hclose.2
  · obtain ⟨k, hgk, hfk⟩ :=
      chudnovskySeymour_compatiblePairHasCommonInterleaver hg hf h.comm
    exact (pairHasCommonLeftInterleaver_of_commonInterleaver
      hgk hfk (le_of_not_ge hdeg) hclose.1).imp fun _ hk => hk.symm

/-- **Chudnovsky--Seymour**, four-way form: for a finite family of real-rooted
polynomials with positive leading coefficients, pairwise compatibility,
pairwise common interleavers, a common interleaver, and family compatibility
are equivalent. -/
theorem chudnovskySeymour_fourWay
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos hrr hpos
    chudnovskySeymour_compatiblePairHasCommonInterleaver

/-- **Chudnovsky--Seymour.** A finite family of real-rooted polynomials with
positive leading coefficients is pairwise compatible if and only if it has a
common interleaver. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay (chudnovskySeymour_fourWay hrr hpos)

/-- **Chudnovsky--Seymour**, common-left form: a finite family of real-rooted
polynomials with positive leading coefficients is pairwise compatible if and
only if it has a common left interleaver. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  ⟨fun hpair =>
    hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver
      (fun f hf => (hrr f hf).2) hpos fun i j hij =>
        chudnovskySeymour_compatiblePairHasCommonLeftInterleaver
          (hpos (fs.get i) (fs.get_mem i)) (hpos (fs.get j) (fs.get_mem j))
          (hpair i j hij),
    fun hcommon => pairwiseCompatible_of_commonLeftInterleaver hcommon hpos⟩

/-- **Chudnovsky--Seymour.** A finite family of real-rooted polynomials with
positive leading coefficients is pairwise compatible if and only if every
nonnegative combination of its members is zero or real-rooted. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  pairwiseCompatible_iff_familyCompatible_of_fourWay (chudnovskySeymour_fourWay hrr hpos)

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
