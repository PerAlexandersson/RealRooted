import RealRooted.CommonInterleaverTwo
import RealRooted.LiuOppositeSigns.ForwardLowDegree

/-!
# Liu common-interleaver consequences

This module contains the positive-deletion and branch-retaining
common-interleaver consequences of Liu's root-count branches.
-/

open Polynomial

namespace RealRooted
namespace LiuOppositeSigns

/-- Normalized deletion-pair compatibility data obtained from Liu branch data.
The four leaves match the four possible positive-leading normalizations of the
left/right deletion branches. -/
def theorem21PositiveDeletionCompatibleBranches (f g : ℝ[X]) : Prop :=
  ∃ r s,
    (Compatible (deleteRootFactor f r) (-g) ∨
        Compatible (-(deleteRootFactor f r)) g) ∨
      (Compatible f (-(deleteRootFactor g s)) ∨
        Compatible (-f) (deleteRootFactor g s))

/-- Branch-retaining common-interleaver data imply the corresponding
normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (h : theorem21DeletionPairCommonInterleaverBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl
      (hleft.1.positiveDeletionPair_compatible_of_commonInterleaver
        hsgn hleft.2)⟩
  · exact ⟨r, s, Or.inr
      (hright.1.positiveDeletionPair_compatible_of_commonInterleaver
        hsgn hright.2)⟩

/-- Positive deletion root-count branches imply the corresponding normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_positiveDeletionCountBranches
    {f g : ℝ[X]} (h : theorem21PositiveDeletionCountBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · rcases hleft with hfg | hfg
    · exact ⟨r, s, Or.inl (Or.inl hfg.compatible)⟩
    · exact ⟨r, s, Or.inl (Or.inr hfg.compatible)⟩
  · rcases hright with hfg | hfg
    · exact ⟨r, s, Or.inr (Or.inl hfg.compatible)⟩
    · exact ⟨r, s, Or.inr (Or.inr hfg.compatible)⟩

/-- Liu root-count branches imply normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    hsgn (theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
      hf_splits hg_splits hsgn h)

end LiuOppositeSigns
end RealRooted
