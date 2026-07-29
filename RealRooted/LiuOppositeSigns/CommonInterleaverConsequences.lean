import RealRooted.LiuOppositeSigns.Corollary22

/-!
# Liu common-interleaver consequences

This module contains the positive-deletion and branch-retaining
common-interleaver consequences derived from Liu Theorem 2.1 packages.
-/

open Polynomial Filter

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

/-- Projection form of the isolated branch-retaining deletion-pair
common-interleaver forward direction. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  hforward hf hg hsgn hcompat

/-- Projection form of the isolated nonconstant branch-retaining deletion-pair
common-interleaver forward direction. -/
theorem
    theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward_nonconstant
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  hforward hf hg hsgn hf_deg hg_deg hcompat

/-- The isolated branch-retaining deletion-pair common-interleaver forward
direction supplies normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    hsgn
    (theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward
      hforward hf hg hsgn hcompat)

/-- The isolated nonconstant branch-retaining deletion-pair common-interleaver
forward direction supplies normalized deletion compatibility branches. -/
theorem
    theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward_nonconstant
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    hsgn
    (theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward_nonconstant
      hforward hf hg hsgn hf_deg hg_deg hcompat)

/-- The isolated forward direction of Liu Theorem 2.1 supplies normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hf hg hsgn hcompat

/-- The isolated nonconstant forward direction of Liu Theorem 2.1 supplies
normalized deletion compatibility branches. -/
theorem
    theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward_nonconstant
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The forward direction of Liu Theorem 2.1 supplies normalized deletion
compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- The nonconstant forward direction of Liu Theorem 2.1 supplies normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The isolated forward direction of Liu Theorem 2.1 supplies
branch-retaining common interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hf hg hsgn hcompat

/-- The isolated nonconstant forward direction of Liu Theorem 2.1 supplies
branch-retaining common interleaver witnesses for the actual deletion pair. -/
theorem
    theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward_nonconstant
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The forward direction of Liu Theorem 2.1 supplies branch-retaining common
interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- The nonconstant forward direction of Liu Theorem 2.1 supplies
branch-retaining common interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Liu Theorem 2.1, restated with branch-retaining deletion-pair
common-interleaver witnesses. -/
theorem compatible_iff_theorem21DeletionPairCommonInterleaverBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g :=
  (theorem21DeletionPairCommonInterleaverIff_of_theorem21CompatibleRootCount
    h) f g hf hg hsgn

/-- The nonconstant Liu Theorem 2.1 statement, restated with branch-retaining
deletion-pair common-interleaver witnesses. -/
theorem compatible_iff_theorem21DeletionPairCommonInterleaverBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g :=
  (theorem21DeletionPairCommonInterleaverIffNonconstant_of_theorem21CompatibleRootCount
    h) f g hf hg hsgn hf_deg hg_deg

/-- Same-degree common-interleaver endpoint from the Liu-side positive-split
root-count leaf. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount
    (hpack : positiveSplitSameDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno)
    |>.pairHasCommonInterleaver_of_sameDegree hdeg

/-- Succ-degree common-interleaver endpoint from the Liu-side positive-split
root-count leaf. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount
    (hpack : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity
      hf_pos hg_pos hfnn hgnn hfg hdeg
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)
    |>.pairHasCommonInterleaver_of_succDegree hdeg

/-- The two positive-split root-count leaves supply the existing
positive-leading compatibility-to-common-interleaver bridge. -/
theorem
    compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    (hsame : positiveSplitSameDegreeRootCountAboveNonRootStatement)
    (hsucc : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (sameDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount hsame)
    (succDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount hsucc)

/-- The strict-upper non-root count leaves also route through the
positive-split package before reaching the common-interleaver endpoint. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot_via_positiveSplit
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    (positiveSplitSameDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot hsame)
    (positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot hsucc)

/-- The checked same-degree analytic count spine and the succ-degree
common-left-interleaver reduction supply the compatible-pair endpoint. -/
theorem
    compatiblePairHasCommonInterleaver_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
    (hsucc : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot_via_positiveSplit
    _root_.RealRooted.posComboNoCommonSameDegreeRootCountAboveNonRootNonneg_from_analytic
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver
      hsucc)

/-- Finite-family Chudnovsky--Seymour package from the Liu-side
positive-split root-count leaves. -/
theorem chudnovskySeymour_fourWay_of_positiveSplitRootCountAboveNonRoot
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : positiveSplitSameDegreeRootCountAboveNonRootStatement)
    (hsucc : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos (fs := fs) hrr hpos
    (compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
      hsame hsucc)

/-- Finite-family Chudnovsky--Seymour package from the checked same-degree
analytic spine and the succ-degree common-left-interleaver reduction. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsucc : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos (fs := fs) hrr hpos
    (compatiblePairHasCommonInterleaver_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
      hsucc)

end LiuOppositeSigns
end RealRooted
