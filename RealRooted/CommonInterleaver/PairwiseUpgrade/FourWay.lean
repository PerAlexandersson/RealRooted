/-
# Four-way finite-family common-interleaver packages

This module assembles pairwise compatibility, pairwise and global common
interleavers, and full family compatibility into reusable finite-family
four-way package witnesses. Equivalence projections and endpoint-specific
corollaries live in `PairwiseUpgrade.FourWay.Equivalences`.
-/
import RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility

open Polynomial

noncomputable section

namespace RealRooted

/-- The finite-family four-way Chudnovsky--Seymour package used by this
project: pairwise compatibility, pairwise common right interleavers, global
common right interleaver, and full nonnegative family compatibility. -/
abbrev ChudnovskySeymourFourWayPackage (fs : List ℝ[X]) : Prop :=
  (PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) ∧
    (PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs) ∧
    (HasCommonInterleaver fs ↔ FamilyCompatible fs)

private theorem chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (h12 : PairwiseCompatible fs ↔ PairwiseHasCommonInterleaver fs) :
    ChudnovskySeymourFourWayPackage fs := by
  have h23 : PairwiseHasCommonInterleaver fs ↔ HasCommonInterleaver fs :=
    ⟨hasCommonInterleaver_of_pairwiseHasCommonInterleaver
        (fun f hf => (hrr f hf).2) hpos,
      pairwiseHasCommonInterleaver_of_commonInterleaver⟩
  have h34 : HasCommonInterleaver fs ↔ FamilyCompatible fs :=
    ⟨fun hcommon => familyCompatible_of_commonInterleaver hcommon hpos,
      fun hfull => h23.1 (h12.1 (pairwiseCompatible_of_familyCompatible hfull))⟩
  exact ⟨h12, h23, h34⟩

/-- Internal four-way assembly shared with the low-degree package. -/
protected theorem PairwiseUpgrade.fourWay_of_pairwiseCommonForward
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hforward : PairwiseCompatible fs → PairwiseHasCommonInterleaver fs) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairwiseCompatible_iff_pairwiseCommon hrr hpos
    ⟨hforward, fun hpair => pairwiseCompatible_of_pairwiseHasCommonInterleaver hpair hpos⟩

/-- The four-way package for a family follows from the two-polynomial
common-interleaver theorem `htwo` by the finite Helly upgrade. -/
theorem chudnovskySeymour_fourWay_of_pairBridgePos
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (htwo :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        Compatible f g →
        ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h) :
    ChudnovskySeymourFourWayPackage fs :=
  PairwiseUpgrade.fourWay_of_pairwiseCommonForward hrr hpos <|
    pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos htwo hpos

end RealRooted
