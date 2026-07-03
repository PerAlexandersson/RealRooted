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

/-- The common-left roadmap target follows from the two expected inputs:
the two-polynomial common-left bridge and the finite-family left Helly upgrade.
-/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    (htwo :
      ∀ ⦃f g : ℝ[X]⦄, Compatible f g → ∃ h : ℝ[X], Prec h f ∧ Prec h g)
    (hglobal :
      ∀ {fs : List ℝ[X]},
        (∀ f ∈ fs, f.Splits) →
        (∀ f ∈ fs, HasPosLeadingCoeff f) →
        PairwiseHasCommonLeftInterleaver fs →
        HasCommonLeftInterleaver fs) :
    chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target :=
  fun {fs} hrr hpos =>
    pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
      (fs := fs) hpos htwo (hglobal (fun f hf => (hrr f hf).2) hpos)

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

/-- Degree-`≤ 1` positive-leading families already satisfy the common-interleaver
form of Chudnovsky--Seymour without the two-polynomial bridge hypothesis. -/
theorem chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  let hfour := chudnovskySeymour_fourWay_of_natDegree_le_one hpos hdeg
  hfour.1.trans hfour.2.1

end RealRooted
