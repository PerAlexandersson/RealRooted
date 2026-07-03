import RealRooted.ChudnovskySeymour
import RealRooted.CommonInterleaverSeq

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
  ChudnovskySeymourFourWayPackage fs

/-- Challenge-facing projection from the four-way package to `1 ↔ 2`. -/
theorem pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_pairwiseHasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `2 ↔ 3`. -/
theorem pairwiseHasCommonInterleaver_iff_commonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseHasCommonInterleaver_iff_hasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `3 ↔ 4`. -/
theorem commonInterleaver_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    HasCommonInterleaver fs ↔ FamilyCompatible fs :=
  RealRooted.hasCommonInterleaver_iff_familyCompatible_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `1 ↔ 3`. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_fourWay hfour

/-- Challenge-facing projection from the four-way package to `1 ↔ 4`. -/
theorem pairwiseCompatible_iff_familyCompatible_of_fourWay
    {fs : List ℝ[X]}
    (hfour : fourWayPackage fs) :
    PairwiseCompatible fs ↔ FamilyCompatible fs :=
  RealRooted.pairwiseCompatible_iff_familyCompatible_of_fourWay hfour

/-- Roadmap target for pairwise compatibility versus common left interleavers. -/
abbrev commonLeftInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_target

/-- Roadmap target for pairwise compatibility versus common right interleavers. -/
abbrev commonInterleaverTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_target

/-- Roadmap target for the nonnegative-coefficient common right interleaver
form. -/
abbrev commonInterleaverNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_nonnegCoeffs_target

/-- Roadmap target for the nonnegative-coefficient finite-family compatibility
form. -/
abbrev familyCompatibleNonnegCoeffsTarget : Prop :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs_target

/-- Full roadmap reduction for the common-left target. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement)
    (hglobal : _root_.RealRooted.CommonLeftInterleaverFamilyUpgradeStatement) :
    commonLeftInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge
    htwo hglobal

/-- Direct roadmap reduction for the common-left target after the finite-family
common-left upgrade has been internalized. -/
theorem commonLeftInterleaverTarget_of_pairwiseLeftBridge_direct
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement) :
    commonLeftInterleaverTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    htwo

/-- Full roadmap reduction for the common-right target. -/
theorem commonInterleaverTarget_of_pairBridge
    (htwo : CompatiblePairHasCommonInterleaverStatement) :
    commonInterleaverTarget :=
  RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairBridge htwo

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the repaired same-degree/succ-degree no-common pair bridges. -/
theorem commonInterleaverNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_pairDegreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the honest degree-split package. -/
theorem commonInterleaverNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_degreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient common-right
target from the boundary-right-pair orientation statement. -/
theorem commonInterleaverNonnegCoeffsTarget_of_boundaryRight
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    commonInterleaverNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_of_boundaryRight_nonneg
    hboundary

/-- Challenge-facing projection from the nonnegative-coefficient common-right
interleaver target to the finite-family compatibility target. -/
theorem familyCompatibleNonnegCoeffsTarget_of_commonInterleaverTarget
    (hcommon : commonInterleaverNonnegCoeffsTarget) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_commonInterleaver_nonneg
    hcommon

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the repaired same-degree/succ-degree no-common pair
bridges. -/
theorem familyCompatibleNonnegCoeffsTarget_of_pairDegreeSplit
    (hsame : PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_pairDegreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the honest degree-split package. -/
theorem familyCompatibleNonnegCoeffsTarget_of_degreeSplit
    (hsame : PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_degreeSplit_nonneg
    hsame hsucc

/-- Challenge-facing reduction for the nonnegative-coefficient finite-family
compatibility target from the boundary-right-pair orientation statement. -/
theorem familyCompatibleNonnegCoeffsTarget_of_boundaryRight
    (hboundary : PosComboNoCommonBoundaryRightPairOrientationStatement) :
    familyCompatibleNonnegCoeffsTarget :=
  chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_of_boundaryRight_nonneg
    hboundary

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

/-- Solved low-degree pairwise/common-interleaver equivalence. -/
theorem pairwiseCompatible_iff_commonInterleaver_of_natDegree_le_one
    {fs : List ℝ[X]}
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hdeg : ∀ f ∈ fs, f.natDegree ≤ 1) :
    PairwiseCompatible fs ↔ HasCommonInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_hasCommonInterleaver_of_natDegree_le_one
    hpos hdeg

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

/-- Challenge-facing direct left-oriented finite-family reduction after the
common-left upgrade: only the two-polynomial common-left bridge remains. -/
theorem pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo : CompatiblePairHasCommonLeftInterleaverStatement) :
    PairwiseCompatible fs ↔ HasCommonLeftInterleaver fs :=
  RealRooted.pairwiseCompatible_iff_commonLeftInterleaver_of_pairwiseLeftBridge_direct
    hrr hpos htwo

end ChudnovskySeymour
end Challenges
end RealRooted
