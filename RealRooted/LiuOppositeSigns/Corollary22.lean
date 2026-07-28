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

/-- Nonconstant linear-endpoint Liu Theorem 2.1 package.  This is a checked
base case for the forward direction together with the existing low-degree
reverse route. -/
def theorem21CompatibleRootCountNatDegreeLeOneNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 1 → g.natDegree ≤ 1 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Isolated nonconstant linear-endpoint forward direction of Liu Theorem 2.1.
The compatibility hypothesis is retained for theorem-shape compatibility, but
the branch condition follows from the endpoint degree bounds. -/
def theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 1 → g.natDegree ≤ 1 →
        Compatible f g → theorem21RootCountBranches f g

/-- The nonconstant linear-endpoint forward direction is checked directly by
deleting the unique largest root on the side selected by the largest-root
comparison. -/
theorem theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstant :
    theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat
  exact theorem21RootCountBranches_of_compatible_natDegree_le_one_nonconstant
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat

/-- Isolated nonconstant linear-endpoint forward direction, restated with
branch-retaining deletion-pair common-interleaver witnesses. -/
def theorem21CompatibleToDeletionPairCommonInterleaverBranchesNatDegreeLeOneNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 1 → g.natDegree ≤ 1 →
        Compatible f g → theorem21DeletionPairCommonInterleaverBranches f g

/-- The checked nonconstant linear-endpoint forward branch supplies the
branch-retaining deletion-pair common-interleaver package. -/
theorem theorem21CompatibleToDeletionPairCommonInterleaverBranchesNatDegreeLeOneNonconstant :
    theorem21CompatibleToDeletionPairCommonInterleaverBranchesNatDegreeLeOneNonconstantStatement :=
  by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat
  exact theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
    hf hg hsgn
    (theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstant
      f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat)

/-- The nonconstant linear-endpoint case of Liu Theorem 2.1 is fully checked:
the forward branch condition follows by root counting after deleting the
unique largest root, and the reverse implication is the existing degree-three
reverse route. -/
theorem theorem21CompatibleRootCountNatDegreeLeOneNonconstant :
    theorem21CompatibleRootCountNatDegreeLeOneNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  constructor
  · exact theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstant
      f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  · intro hbranches
    exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_three
      hf hg hsgn hfdeg_ne hgdeg_ne
      (hfdeg_le.trans (by norm_num)) (hgdeg_le.trans (by norm_num))
      hbranches

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

/-- Nonconstant low-degree bounded Liu equivalence through endpoint degree
two, assuming the isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact hforward hf hg hsgn hfdeg_ne hgdeg_ne
  · intro hbranches
    exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_two
      hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hbranches

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
  · have hcommon : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r := by
      by_contra hmissing
      exact hno (by
        intro r hfr hgr
        exact hmissing ⟨r, hfr, hgr⟩)
    rcases hcommon with ⟨r, hfr, hgr⟩
    exact Or.inr
      ⟨r, hfr, hgr,
        compatible_deleteRootFactor_of_common_root hcompat hfr hgr⟩

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

/-- Reassemble the bounded endpoint-degree-two theorem package from the full
forward direction and the bounded endpoint-degree-two reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeTwoStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Current bounded endpoint-degree-two Liu package, assuming the isolated
forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_reverse
    hforward theorem21RootCountBranchesToCompatible_of_endpoint_le_two

/-- Reassemble the bounded endpoint-degree-two theorem package from the
branch-retaining common-interleaver forward direction and a
predicate-restricted reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranches_of_commonForward hforward)
    (fun hf hg hsgn hbranches => hreverse hf hg hsgn hbranches)

/-- Reassemble the bounded endpoint-degree-two theorem package from the full
forward direction and a predicate-restricted reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreverse

/-- Current bounded endpoint-degree-two Liu package from endpoint
factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_endpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)

/-- Current bounded endpoint-degree-two Liu package from endpoint
factor-return case packages and the full root-count forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_endpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)

/-- Current bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases and the full root-count forward
direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current bounded endpoint-degree-two Liu package, assuming the isolated
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_two

/-- Reassemble the nonconstant bounded endpoint-degree-two theorem package
from the nonconstant forward direction and the bounded endpoint-degree-two
reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          f.natDegree ≠ 0 → g.natDegree ≠ 0 →
            theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne
  exact ⟨hforward hf hg hsgn hfdeg_ne hgdeg_ne,
    hreverse hf hg hsgn hfdeg_ne hgdeg_ne⟩

/-- Current nonconstant bounded endpoint-degree-two Liu package, assuming the
isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_reverse
    hforward theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_two

/-- Reassemble the nonconstant bounded endpoint-degree-two theorem package
from the branch-retaining common-interleaver forward direction and a
predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesNonconstant_of_commonForward
      hforward)
    (fun hf hg hsgn hfdeg_ne hgdeg_ne hbranches =>
      hreverse hf hg hsgn hfdeg_ne hgdeg_ne hbranches)

/-- Reassemble the nonconstant bounded endpoint-degree-two theorem package
from the nonconstant forward direction and a predicate-restricted reverse
direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreverse

/-- Current nonconstant bounded endpoint-degree-two Liu package from endpoint
factor-return case packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_endpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)

/-- Current nonconstant bounded endpoint-degree-two Liu package from endpoint
factor-return case packages and the nonconstant root-count forward direction.
-/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_endpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_xSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)

/-- Current nonconstant bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases and the nonconstant root-count forward
direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant bounded endpoint-degree-two Liu package, assuming the
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_two

/-- The bounded endpoint-degree-two package restricts to the ordinary
low-degree statement with explicit endpoint degree bounds. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwo_of_endpointLeTwo
    (h : theorem21CompatibleRootCountEndpointLeTwoStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn).1
  · intro hbranches
    exact (h f g hf hg hsgn).2
      (theorem21RootCountBranchesEndpointLeTwo_of_natDegree_le_two
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-two package restricts to its nonconstant
endpoint-degree-two form. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_endpointLeTwo
    (h : theorem21CompatibleRootCountEndpointLeTwoStatement) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne
  exact h f g hf hg hsgn

/-- The ordinary endpoint-degree-two Liu package restricts to its nonconstant
form. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_natDegreeLeTwo
    (h : theorem21CompatibleRootCountNatDegreeLeTwoStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne hfdeg hgdeg
  exact h f g hf hg hsgn hfdeg hgdeg

/-- The nonconstant bounded endpoint-degree-two package restricts to the
ordinary nonconstant low-degree statement with explicit endpoint degree bounds.
-/
theorem
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_endpointLeTwoNonconstant
    (h : theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).1
  · intro hbranches
    exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).2
      (theorem21RootCountBranchesEndpointLeTwo_of_natDegree_le_two
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-two package restricts directly to the
ordinary nonconstant low-degree statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_endpointLeTwo
    (h : theorem21CompatibleRootCountEndpointLeTwoStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_natDegreeLeTwo
    (theorem21CompatibleRootCountNatDegreeLeTwo_of_endpointLeTwo h)

/-- Current low-degree endpoint-two Liu theorem package from a
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwo_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoStatement :=
  theorem21CompatibleRootCountNatDegreeLeTwo_of_endpointLeTwo
    (theorem21CompatibleRootCountEndpointLeTwo_of_commonForward hforward)

/-- Current nonconstant low-degree endpoint-two Liu theorem package from a
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_endpointLeTwoNonconstant
    (theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward
      hforward)

end LiuOppositeSigns
end RealRooted
