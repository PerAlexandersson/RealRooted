import RealRooted.LiuOppositeSigns.ForwardLowDegree

/-!
# Liu bounded theorem packages

This module contains bounded endpoint and low-degree theorem packages derived
from the reverse assembly for Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Bounded Liu Theorem 2.1 package through endpoint degree two.  The forward
direction is the ordinary Liu forward direction, while the reverse direction is
restricted to branch data whose selected lower-degree endpoint has degree at
most two. -/
def theorem21CompatibleRootCountEndpointLeTwoStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g → theorem21RootCountBranches f g) ∧
      (theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g)

/-- Nonconstant bounded Liu Theorem 2.1 package through endpoint degree two.
-/
def theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g → theorem21RootCountBranches f g) ∧
        (theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g)

/-- Bounded Liu Theorem 2.1 package through endpoint degree three.  The forward
direction is the ordinary Liu forward direction, while the reverse direction is
restricted to branch data whose selected lower-degree endpoint has degree at
most three. -/
def theorem21CompatibleRootCountEndpointLeThreeStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g → theorem21RootCountBranches f g) ∧
      (theorem21RootCountBranchesEndpointLeThree f g → Compatible f g)

/-- Nonconstant bounded Liu Theorem 2.1 package through endpoint degree three.
-/
def theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g → theorem21RootCountBranches f g) ∧
        (theorem21RootCountBranchesEndpointLeThree f g → Compatible f g)

/-- Low-degree Liu Theorem 2.1 package through endpoint degree three, stated
with the ordinary branch predicate and explicit endpoint degree bounds. -/
def theorem21CompatibleRootCountNatDegreeLeThreeStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≤ 3 → g.natDegree ≤ 3 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant low-degree Liu Theorem 2.1 package through endpoint degree
three, stated with the ordinary branch predicate and explicit endpoint degree
bounds. -/
def theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 3 → g.natDegree ≤ 3 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Low-degree Liu Theorem 2.1 package through endpoint degree two, stated
with the ordinary branch predicate and explicit endpoint degree bounds. -/
def theorem21CompatibleRootCountNatDegreeLeTwoStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≤ 2 → g.natDegree ≤ 2 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant low-degree Liu Theorem 2.1 package through endpoint degree
two, stated with the ordinary branch predicate and explicit endpoint degree
bounds. -/
def theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant no-common-root low-degree Liu Theorem 2.1 package through
endpoint degree two. -/
def theorem21CompatibleRootCountNatDegreeLeTwoNoCommonNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant no-common-root low-degree forward direction through endpoint
degree two. -/
def theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        Compatible f g → theorem21RootCountBranches f g

/-- Corrected nonconstant low-degree Liu package through endpoint degree two,
using an explicit common-root deletion branch in the conclusion. -/
def theorem21CompatibleRootCountWithCommonNatDegreeLeTwoNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        (Compatible f g ↔ theorem21RootCountBranchesWithCommon f g)

/-- Corrected nonconstant low-degree forward direction through endpoint degree
two, with an explicit common-root deletion branch. -/
def
    theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        Compatible f g → theorem21RootCountBranchesWithCommon f g

/-- Low-degree bounded Liu equivalence through endpoint degree two, assuming
the isolated forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwo_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  constructor
  · exact hforward hf hg hsgn
  · intro hbranches
    exact theorem21RootCountBranchesToCompatible_of_natDegree_le_two
      hf hg hsgn hfdeg hgdeg hbranches

/-- The nonconstant no-common-root low-degree forward direction through
endpoint degree two is checked directly. -/
theorem theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstant :
    theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstantStatement :=
  by
  intro f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg hcompat
  exact theorem21RootCountBranches_of_compatible_natDegree_le_two_of_no_common
    hf hg hsgn hcompat hno hfdeg_ne hgdeg_ne hfdeg hgdeg

/-- The nonconstant no-common-root low-degree Liu equivalence through endpoint
degree two is fully checked. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNoCommonNonconstant :
    theorem21CompatibleRootCountNatDegreeLeTwoNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact
      theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstant
        f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg
  · intro hbranches
    exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_two
      hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hbranches

/-- The corrected nonconstant low-degree forward direction through endpoint
degree two follows from the no-common forward theorem and the automatic
common-root deletion branch. -/
theorem
    theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstant :
    theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstantStatement :=
  by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hcompat
  by_cases hno : NoCommonRoots f g
  · exact Or.inl
      (theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstant
        f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg hcompat)
  · exact Or.inr
      (CommonRootDeletionCompatibleBranch.of_compatible_of_not_noCommonRoots
        hcompat hno)

/-- The corrected nonconstant low-degree Liu equivalence through endpoint
degree two is fully checked, with common roots handled by an explicit deletion
branch. -/
theorem theorem21CompatibleRootCountWithCommonNatDegreeLeTwoNonconstant :
    theorem21CompatibleRootCountWithCommonNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact
      theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstant
        f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  · intro hbranches
    rcases hbranches with hbranches | hcommon
    · exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_two
        hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hbranches
    · exact CommonRootDeletionCompatibleBranch.compatible hcommon

/-- The bounded endpoint-degree-three package restricts to the ordinary
low-degree statement with explicit endpoint degree bounds. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_endpointLeThree
    (h : theorem21CompatibleRootCountEndpointLeThreeStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn).1
  · intro hbranches
    exact (h f g hf hg hsgn).2
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-three package restricts to the nonconstant
bounded endpoint-degree-three package. -/
theorem theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_endpointLeThree
    (h : theorem21CompatibleRootCountEndpointLeThreeStatement) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne
  exact h f g hf hg hsgn

/-- The ordinary low-degree Liu package restricts to its nonconstant form. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_natDegreeLeThree
    (h : theorem21CompatibleRootCountNatDegreeLeThreeStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne hfdeg hgdeg
  exact h f g hf hg hsgn hfdeg hgdeg

/-- The bounded endpoint-degree-three nonconstant package restricts to the
ordinary nonconstant low-degree statement with explicit endpoint degree bounds.
-/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_endpointLeThreeNonconstant
    (h : theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).1
  · intro hbranches
    exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).2
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-three package restricts directly to the
ordinary nonconstant low-degree statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_endpointLeThree
    (h : theorem21CompatibleRootCountEndpointLeThreeStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_natDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThree_of_endpointLeThree h)

/-- Liu Corollary 2.2: compatible real-rooted polynomials with opposite leading
signs have degree gap at most two. -/
def corollary22DegreeDiffStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Low-degree form of Liu Corollary 2.2 through endpoint degree three. -/
def corollary22DegreeDiffNatDegreeLeThreeStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≤ 3 → g.natDegree ≤ 3 →
      Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Nonconstant low-degree form of Liu Corollary 2.2 through endpoint degree
three. -/
def corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 3 → g.natDegree ≤ 3 →
        Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Projection form of `corollary22DegreeDiffStatement`. -/
theorem corollary22DegreeDiff
    (h : corollary22DegreeDiffStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hcompat

/-- Liu Corollary 2.2 follows from the isolated branch-retaining
common-interleaver forward direction. -/
theorem corollary22DegreeDiff_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    corollary22DegreeDiffStatement :=
  fun _ _ hf hg hsgn hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
        (hforward hf hg hsgn hcompat))

/-- Liu Corollary 2.2 follows from the isolated forward direction of
Theorem 2.1. -/
theorem corollary22DegreeDiff_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    corollary22DegreeDiffStatement :=
  corollary22DegreeDiff_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)

/-- Liu Corollary 2.2 follows from the Theorem 2.1 compatibility criterion. -/
theorem corollary22DegreeDiff_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    corollary22DegreeDiffStatement :=
  corollary22DegreeDiff_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)

end LiuOppositeSigns
end RealRooted
