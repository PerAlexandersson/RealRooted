import RealRooted.ClosedSegmentCountEqFromAnalytic
import RealRooted.CommonInterleaverTwo
import RealRooted.SameDegreeCountFromAnalytic

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
    (hglobal : (∀ {fs : List ℝ[X]},
        (∀ f ∈ fs, f.Splits) →
        (∀ f ∈ fs, HasPosLeadingCoeff f) →
        PairwiseHasCommonLeftInterleaver fs →
        HasCommonLeftInterleaver fs)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target :=
  fun {fs} hrr hpos =>
    pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
      (fs := fs) hpos (hglobal (fun f hf => (hrr f hf).2) hpos)

/-- Direct roadmap wrapper after the finite-family common-left upgrade: the
common-left Chudnovsky--Seymour target now only needs the two-polynomial
common-left bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    : chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target :=
  fun {fs} hrr hpos =>
    pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
      (fs := fs) (fun f hf => (hrr f hf).2) hpos

/-- The common-left roadmap target follows from the positive-leading common
right two-polynomial bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairBridge
    (hright : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        Compatible f g →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
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
    (compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
      posComboNoCommonSameDegreePairHasCommonInterleaverNonneg_from_analytic
      succDegreePairHasCommonInterleaver_nonneg_of_local_lower_counts)

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

/-- Chudnovsky--Seymour pairwise-to-family compatibility equivalence.

This is the `1 ↔ 4` Chudnovsky--Seymour surface under the same standard
real-rooted/splits and positive-leading hypotheses as
`chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target`. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f) :
    PairwiseCompatible fs ↔ FamilyCompatible fs := by
  sorry

private abbrev chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target : Prop :=
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
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_pairBridgePos hrr hpos
      (fun _ _ hf hg h => compatiblePairHasCommonInterleaver hf hg h)

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
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairBridge :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge

/-- The roadmap target follows from the same-degree and successor-degree
two-polynomial bridges. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        Compatible f g →
        g.natDegree = f.natDegree →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        Compatible f g →
        g.natDegree = f.natDegree + 1 →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_compatibleDegreeSplit
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from the
same-degree and successor-degree two-polynomial bridges. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_degreeSplit
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        Compatible f g →
        g.natDegree = f.natDegree →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        Compatible f g →
        g.natDegree = f.natDegree + 1 →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit
      hsame hsucc)

/-- The roadmap target follows from the nonnegative-shift route, with the
succ-degree branch discharged by the affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_nonnegShift
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_via_nonnegShift
      hrr hpos hsame haffBridge

/-- The finite-family compatibility roadmap target follows from the
nonnegative-shift route, with the succ-degree branch discharged by the
affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_nonnegShift
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_nonnegShift
      hsame haffBridge)

/-- The roadmap target follows from the concrete slot-data endpoints after the
nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_slotData
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (f ≠ 0 ∧ f.Splits) ∧
          ∀ j, j < f.natDegree + 1 →
            ∀ (hjf : j < (rootSeqDesc f).length + 1)
              (hjg : j < (rootSeqDesc g).length + 1),
              (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
                rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_slotData_via_nonnegShift
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from the concrete
slot-data endpoints after the nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_slotData
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (f ≠ 0 ∧ f.Splits) ∧
          ∀ j, j < f.natDegree + 1 →
            ∀ (hjf : j < (rootSeqDesc f).length + 1)
              (hjg : j < (rootSeqDesc g).length + 1),
              (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
                rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_slotData
      hsame hsucc)

/-- The roadmap target follows from the root-crossing formulations of the
same-degree and succ-degree endpoints after the nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsplit : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        f.Splits))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_via_nonnegShift
      hrr hpos hsame hsplit hsucc

/-- The finite-family compatibility roadmap target follows from the
root-crossing formulations after the nonnegative-shift reduction. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsplit : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        f.Splits))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing
      hsame hsplit hsucc)

/-- The roadmap target follows from the root-crossing formulations alone:
root continuity supplies the succ-degree left endpoint. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_direct
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from root-crossing
alone; root continuity supplies the succ-degree left endpoint. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing_direct
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_direct
      hsame hsucc)

/-- The roadmap target follows from the root-crossing formulations once the
succ-degree left endpoint is supplied by the PF/ASW route. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forward_asw
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from root-crossing
once the succ-degree left endpoint is supplied by the PF/ASW route. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forward_asw
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forward_asw
      hsame hsucc)

/-- The roadmap target follows from the root-crossing formulations once the
succ-degree left endpoint is supplied by the splitting-only ASW target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forwardASWSplits
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  fun hrr hpos =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_rootCrossing_and_forward_asw_splits
      hrr hpos hsame hsucc

/-- The finite-family compatibility roadmap target follows from root-crossing
once the succ-degree left endpoint is supplied by the splitting-only ASW
target. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_rootCrossing_and_forwardASWSplits
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_rootCrossing_and_forwardASWSplits
      hsame hsucc)

/-- The roadmap target also follows from the same-degree root-crossing
formulation and the affine-family bridge, avoiding the separate succ-degree
root-crossing branch. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeCrossing_affineFamily
    (_hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (_haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge

/-- The finite-family compatibility roadmap target follows from same-degree
root-crossing and the affine-family bridge. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeCrossing_affineFamily
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver
    (chudnovskySeymour_commonInterleaver_of_sameDegreeCrossing_affineFamily
      hsame haffBridge)

/-- The nonnegative four-way package target follows from the root-crossing
formulations once the succ-degree left endpoint is supplied by the
splitting-only ASW target. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos _ =>
    chudnovskySeymour_fourWay_of_rootCrossing_and_forward_asw_splits
      hrr hpos hsame hsucc

/-- The nonnegative four-way package target follows from the root-crossing
formulations alone; root continuity supplies the succ-degree left endpoint. -/
theorem chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos _ =>
    RealRooted.chudnovskySeymour_fourWay_of_rootCrossing
      hrr hpos hsame hsucc

/-- The nonnegative four-way package target follows from lower-threshold
root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCount_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- The nonnegative four-way package target follows from same-degree
lower-threshold root counts and succ-degree upper-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_rootCountAbove_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCount hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- The nonnegative four-way package target follows from same-degree
upper-threshold root counts and succ-degree lower-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_sameRootCountAbove_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCount hsucc)

/-- The nonnegative four-way package target follows from upper-threshold
root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCountAboveBoth_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAbove hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAbove hsucc)

/-- The nonnegative four-way package target follows from common-non-root
lower-threshold root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCountNonRoot_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- The nonnegative four-way package target follows from same-degree
common-non-root lower-threshold root counts and succ-degree common-non-root
upper-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_rootCountAboveNonRoot_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- The nonnegative four-way package target follows from same-degree
common-non-root upper-threshold root counts and succ-degree common-non-root
lower-threshold root counts. -/
theorem chudnovskySeymour_fourWay_of_sameRootCountAboveNonRoot_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountNonRoot hsucc)

/-- The nonnegative four-way package target follows from common-non-root
upper-threshold root-count formulations in both degree branches. -/
theorem chudnovskySeymour_fourWay_of_rootCountAboveBothNonRoot_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCrossing_nonneg
    (posComboNoCommonSameDegreeRootCrossing_of_rootCountAboveNonRoot hsame)
    (posComboNoCommonSuccDegreeRootCrossing_of_rootCountAboveNonRoot hsucc)

/-- The nonnegative four-way package target follows from same-degree
root-crossing and the affine-family bridge for the succ-degree branch. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
        hsame hsucc hrr hpos hnn)

/-- The nonnegative common-interleaver target follows from the root-crossing
formulations alone. -/
theorem chudnovskySeymour_commonInterleaver_of_rootCrossing_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_nonneg
        hsame hsucc hrr hpos hnn)

/-- The nonnegative common-interleaver target follows from same-degree
root-crossing and the affine-family bridge. -/
theorem chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay
      (chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_affineFamily_nonneg
        hsame haffBridge hrr hpos hnn)

/-- The nonnegative finite-family compatibility target follows from the
root-crossing formulations and splitting-only ASW. -/
theorem
    chudnovskySeymour_familyCompatible_of_rootCrossing_forwardASWSplits_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_forwardASWSplits_nonneg
        hsame hsucc hrr hpos hnn)

/-- The nonnegative finite-family compatibility target follows from the
root-crossing formulations alone. -/
theorem chudnovskySeymour_familyCompatible_of_rootCrossing_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        f.Splits →
        (∀ j, 1 ≤ j → j ≤ f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    pairwiseCompatible_iff_familyCompatible_of_fourWay
      (chudnovskySeymour_fourWay_of_rootCrossing_nonneg
        hsame hsucc hrr hpos hnn)

/-- The nonnegative finite-family compatibility target follows from
same-degree root-crossing and the affine-family bridge. -/
theorem chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_affineFamily_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
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
    (hstep : (∀ ⦃f g : ℝ[X]⦄,
        PosComboRealRooted f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_noCommonOrientation_and_nonnegCoeffs
      hrr hpos hnn hstep

/-- The nonnegative-coefficient common-interleaver target follows from the
no-common orientation core. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_noCommonOrientation_nonneg
    (hstep : (∀ ⦃f g : ℝ[X]⦄,
        PosComboRealRooted f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_noCommonOrientation_nonneg hstep)

/-- The nonnegative four-way package target follows from the repaired
same-degree and successor-degree no-common pair bridges. -/
theorem chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
      hrr hpos hnn hsame hsucc

/-- The nonnegative-coefficient roadmap target follows from the repaired
same-degree and successor-degree no-common pair bridges. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg hsame hsucc)

/-- The proved #41 same-degree endpoint and #42 successor-degree endpoint close
the nonnegative-coefficient four-way Chudnovsky--Seymour package. -/
theorem chudnovskySeymour_fourWay_nonnegCoeffs :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg
    posComboNoCommonSameDegreePairHasCommonInterleaverNonneg_from_analytic
    succDegreePairHasCommonInterleaver_nonneg_of_local_lower_counts

/-- The proved #41 same-degree endpoint and #42 successor-degree endpoint close
the nonnegative-coefficient pairwise/common-interleaver form of
Chudnovsky--Seymour. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    chudnovskySeymour_fourWay_nonnegCoeffs

/-- The nonnegative-coefficient finite-family compatibility form follows from
the proved #41/#42 endpoint package. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_fourWay_nonneg
    chudnovskySeymour_fourWay_nonnegCoeffs

/-- The nonnegative four-way package target follows from the honest same-degree
orientation alternative and successor-degree bridge. -/
theorem chudnovskySeymour_fourWay_of_degreeSplit_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_degreeSplit_and_nonnegCoeffs
      hrr hpos hnn hsame hsucc

/-- The nonnegative-coefficient roadmap target follows from the honest
same-degree orientation alternative and successor-degree bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_degreeSplit_nonneg hsame hsucc)

/-- The nonnegative four-way package target follows from the repaired
same-degree bridge and the affine-family bridge for the successor-degree
branch. -/
theorem chudnovskySeymour_fourWayTarget_of_sameDegreePair_and_affineFamily_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_sameDegreePair_and_affineFamily_nonneg
      hrr hpos hnn hsame haffBridge

/-- The nonnegative-coefficient common-interleaver target follows from the
repaired same-degree bridge and the affine-family bridge for the
successor-degree branch. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreePair_affineFamily_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWayTarget_of_sameDegreePair_and_affineFamily_nonneg
      hsame haffBridge)

/-- The nonnegative four-way package target follows from the all-combinations
bridge. -/
theorem chudnovskySeymour_fourWay_of_allComboBridge_nonneg
    (hallBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        AllComboRealRooted f g)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_allComboBridge_and_nonnegCoeffs
      hrr hpos hnn hallBridge

/-- The nonnegative-coefficient common-interleaver target follows from the
all-combinations bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_allComboBridge_nonneg
    (hallBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        AllComboRealRooted f g)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_allComboBridge_nonneg hallBridge)

/-- The nonnegative four-way package target follows from the affine-family
bridge. -/
theorem chudnovskySeymour_fourWay_of_affineFamilyBridge_nonneg
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_affineFamilyBridge_and_nonnegCoeffs
      hrr hpos hnn haffBridge

/-- The nonnegative-coefficient common-interleaver target follows from the
affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_affineFamilyBridge_nonneg
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_affineFamilyBridge_nonneg haffBridge)

/-- The nonnegative four-way package target follows from the
boundary-right-pair orientation statement. -/
theorem chudnovskySeymour_fourWay_of_boundaryRight_nonneg
    (hboundary : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃t : ℝ⦄, 0 < t →
          Prec (C t * f + g) (X * f) ∨ Prec (X * f) (C t * f + g))) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  fun hrr hpos hnn =>
    chudnovskySeymour_fourWay_of_boundaryRightPairOrientation_and_nonnegCoeffs
      hrr hpos hnn hboundary

/-- The nonnegative-coefficient roadmap target follows from the
boundary-right-pair orientation statement. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
    (hboundary : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃t : ℝ⦄, 0 < t →
          Prec (C t * f + g) (X * f) ∨ Prec (X * f) (C t * f + g))) :
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
    (hstep : (∀ ⦃f g : ℝ[X]⦄,
        PosComboRealRooted f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_noCommonOrientation_nonneg
      hstep)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the repaired same-degree and successor-degree no-common pair bridges. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
      hsame hsucc)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the honest same-degree orientation alternative and successor-degree
bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_degreeSplit_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
      hsame hsucc)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the repaired same-degree bridge and the affine-family bridge for the
successor-degree branch. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreePair_affineFamily_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_commonInterleaver_of_sameDegreePair_affineFamily_nonneg
      hsame haffBridge)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the all-combinations bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_allComboBridge_nonneg
    (hallBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        AllComboRealRooted f g)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_allComboBridge_nonneg
      hallBridge)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the affine-family bridge. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_affineFamilyBridge_nonneg
    (haffBridge : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_affineFamilyBridge_nonneg
      haffBridge)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the boundary-right-pair orientation statement. -/
theorem
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_boundaryRight_nonneg
    (hboundary : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ ⦃t : ℝ⦄, 0 < t →
          Prec (C t * f + g) (X * f) ∨ Prec (X * f) (C t * f + g))) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
      hboundary)

/-- The nonnegative four-way package target follows from the same-degree
common-non-root root-count leaf and the direct compatible succ-degree
closed-segment endpoint count-equality route. -/
theorem
    chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_rootCountAboveNonRoot_nonneg hsame
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hsucc)

/-- The nonnegative-coefficient common-interleaver target follows from the
same-degree common-non-root root-count leaf and the direct compatible
succ-degree closed-segment endpoint count-equality route. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
      hsame hsucc)

/-- The nonnegative-coefficient finite-family compatibility target follows
from the same-degree common-non-root root-count leaf and the direct compatible
succ-degree closed-segment endpoint count-equality route. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_fourWay_nonneg
    (chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
      hsame hsucc)

/-- The nonnegative four-way package target also follows from the same-degree
common-non-root root-count leaf and the exact lower-threshold endpoint-sign
count-equality form of the direct compatible succ-degree route. -/
theorem
    chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameRootCountNonRoot_and_succClosedSegmentCountEq_nonneg
    hsame (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-- The nonnegative-coefficient common-interleaver target follows from the
same-degree common-non-root root-count leaf and the exact lower-threshold
endpoint-sign count-equality form of the direct compatible succ-degree route. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameRootCountNonRoot_and_succLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_pairDegreeSplit_nonneg hsame
    (succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq hsucc)

/-- Nonnegative-coefficient common-interleaver target from the repaired
same-degree pair endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg hsame
    (succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq hsucc)

/-- Nonnegative-coefficient finite-family compatibility target from the
repaired same-degree pair endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_nonneg hsame
    (succDegreePairHasCommonInterleaver_nonneg_of_closedSegmentCountEq hsucc)

/-- Nonnegative four-way package target from the repaired same-degree pair
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    hsame (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-- Nonnegative-coefficient common-interleaver target from the repaired
same-degree pair endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg hsame
    (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-- Nonnegative-coefficient finite-family compatibility target from the
repaired same-degree pair endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∃ h : ℝ[X], Prec f h ∧ Prec g h))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg hsame
    (compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq hsucc)

/-! #### Same-degree slot-data endpoint with the direct #42 route

The same-degree slot-data endpoint feeds the repaired same-degree pair endpoint
through `sameDegreePairHasCommonInterleaver_nonneg_of_slotData`. -/

/-- Nonnegative four-way package target from the same-degree slot-data endpoint
and the #42 compatible succ-degree closed-segment endpoint count equality. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeSlotData_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
slot-data endpoint and the #42 compatible succ-degree closed-segment endpoint
count equality. -/
theorem
    chudnovskySeymour_commonInterleaver_of_sameDegreeSlotData_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree slot-data endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeSlotData_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative four-way package target from the same-degree slot-data endpoint
and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeSlotData_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
slot-data endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
  chudnovskySeymour_commonInterleaver_of_sameDegreeSlotData_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_slotData hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree slot-data endpoint and the #42 exact lower-threshold endpoint-sign
count equality leaf. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeSlotData_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ j, j < f.natDegree + 1 →
          ∀ (hjf : j < (rootSeqDesc f).length + 1)
            (hjg : j < (rootSeqDesc g).length + 1),
            (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
              rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
root-crossing endpoint and the #42 compatible succ-degree closed-segment
endpoint count equality. -/
theorem
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree root-crossing endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
    chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative four-way package target from the same-degree root-crossing
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCrossing_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
root-crossing endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCrossing_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCrossing hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree root-crossing endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCrossing_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < f.natDegree →
            (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree lower
root-count endpoint and the #42 compatible succ-degree closed-segment endpoint
count equality. -/
theorem
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCount_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree lower root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCount_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative four-way package target from the same-degree lower root-count
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem chudnovskySeymour_fourWay_of_sameDegreeRootCount_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree lower
root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCount_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCount hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree lower root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCount_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree upper
root-count endpoint and the #42 compatible succ-degree closed-segment endpoint
count equality. -/
theorem
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCountAbove_and_succClosedSegmentEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree upper root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCountAbove_and_succClosedSegmentCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative four-way package target from the same-degree upper root-count
endpoint and the #42 exact lower-threshold endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_fourWay_of_sameDegreeRootCountAbove_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree upper
root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
  chudnovskySeymour_commonInterleaver_of_sameDegreeRootCountAbove_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAbove hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree upper root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_familyCompatible_of_sameDegreeRootCountAbove_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ,
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root upper root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
  chudnovskySeymour_commonInterleaver_of_rootCountAboveNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root upper root-count endpoint and the #42 compatible
succ-degree closed-segment endpoint count equality. -/
theorem
  chudnovskySeymour_familyCompatible_of_rootCountAboveNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative four-way package target from the same-degree common-non-root
upper root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
  chudnovskySeymour_fourWay_of_rootCountAboveNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root upper root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_commonInterleaver_of_rootCountAboveNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root upper root-count endpoint and the #42 exact
lower-threshold endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_familyCompatible_of_rootCountAboveNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root lower root-count endpoint and the #42 compatible succ-degree
closed-segment endpoint count equality. -/
theorem
  chudnovskySeymour_commonInterleaver_of_rootCountNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root lower root-count endpoint and the #42 compatible
succ-degree closed-segment endpoint count equality. -/
theorem
  chudnovskySeymour_familyCompatible_of_rootCountNonRoot_and_succClosedSegmentEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
            ¬ (C (1 - β) * f + C β * g).IsRoot x) →
          (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card)) :
    chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target :=
  chudnovskySeymour_familyCompatible_of_sameDegreePair_and_succClosedSegmentCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative four-way package target from the same-degree common-non-root
lower root-count endpoint and the #42 exact lower-threshold endpoint-sign count
equality leaf. -/
theorem
  chudnovskySeymour_fourWay_of_sameDegreeRootCountNonRoot_and_succEndpointSignLowerCountEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_fourWay_nonnegCoeffs_target :=
  chudnovskySeymour_fourWay_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient common-interleaver target from the same-degree
common-non-root lower root-count endpoint and the #42 exact lower-threshold
endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_commonInterleaver_of_rootCountNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
    chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target :=
  chudnovskySeymour_commonInterleaver_of_sameDegreePair_and_succEndpointSignLowerCountEq_nonneg
    (sameDegreePairHasCommonInterleaver_nonneg_of_rootCountNonRoot hsame) hsucc

/-- Nonnegative-coefficient finite-family compatibility target from the
same-degree common-non-root lower root-count endpoint and the #42 exact
lower-threshold endpoint-sign count equality leaf. -/
theorem
  chudnovskySeymour_familyCompatible_of_rootCountNonRoot_and_succEndpointSignLowerEq_nonneg
    (hsame : (∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        g.natDegree = f.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1))
    (hsucc : (∀ ⦃f g : ℝ[X]⦄,
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          0 < f.eval x * g.eval x →
          ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1)) :
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
