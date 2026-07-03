import RealRooted.ChudnovskySeymour

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
  (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
    (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
    (HasCommonInterleaver fs ↔ FamilyCompatible fs)

/-- Roadmap target for pairwise compatibility versus common left interleavers. -/
abbrev commonLeftInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target

/-- Roadmap target for pairwise compatibility versus common right interleavers. -/
abbrev commonInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target

/-- Full roadmap reduction for the common-left target. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal :
      ∀ {fs : List ℝ[X]},
        (∀ f ∈ fs, f.Splits) →
        (∀ f ∈ fs, HasPosLeadingCoeff f) →
        PairwiseHasCommonLeftInterleaver fs →
        HasCommonLeftInterleaver fs) :
    commonLeftInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    htwo hglobal

/-- Full roadmap reduction for the common-right target. -/
theorem commonInterleaverTarget_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    commonInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge htwo

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

/-- Solved low-degree pairwise/full-family compatibility equivalence. -/
theorem pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  RealRooted.pairwiseCompatible_iff_familyCompatible_of_natDegree_le_one
    hpos hdeg

/-- Challenge-facing reduction for the left-oriented common-interleaver target. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal : PairwiseHasCommonLeftInterleaver fs → HasCommonLeftInterleaver fs) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    hpos htwo hglobal

end ChudnovskySeymour
end Challenges
end RealRooted
