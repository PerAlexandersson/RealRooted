/-
# Pairwise finite-family common-interleaver upgrades

This module lifts a two-polynomial common-interleaver theorem to pairwise
common-interleaver witnesses for a family. Generic global and full-family compatibility
packaging lives in `PairwiseUpgrade.FamilyCompatibility`.
-/
import RealRooted.CommonInterleaver.PairBridge

open Polynomial

noncomputable section

namespace RealRooted

/-- A pairwise compatible family with positive leading coefficients has pairwise
common interleavers, given the two-polynomial common-interleaver theorem
`htwo`. -/
theorem pairwiseHasCommonInterleaver_of_pairwiseCompatible_of_pairBridgePos
    {fs : List ℝ[X]}
    (htwo :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        Compatible f g →
        ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) :
    PairwiseHasCommonInterleaver fs :=
  fun i j hij =>
    htwo
      (hpos (fs.get i) (List.get_mem _ _))
      (hpos (fs.get j) (List.get_mem _ _))
      (hpair i j hij)

end RealRooted
