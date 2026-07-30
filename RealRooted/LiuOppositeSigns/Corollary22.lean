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

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and the bounded reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          theorem21RootCountBranchesEndpointLeThree f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeThreeStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Reassemble the bounded endpoint-degree-three theorem package from the
branch-retaining common-interleaver forward direction and a
predicate-restricted reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranches_of_commonForward hforward)
    (fun hf hg hsgn hbranches => hreverse hf hg hsgn hbranches)

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and a predicate-restricted reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreverse

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and endpoint factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)

/-- Reassemble the bounded endpoint-degree-three theorem package from the
full root-count forward direction and endpoint factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_endpointDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and left endpoint factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_leftEndpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
      hcases)

/-- Reassemble the bounded endpoint-degree-three theorem package from the
full root-count forward direction and left endpoint factor-return case
packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_leftEndpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and bundled predicate-restricted x-subtraction cases. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)

/-- Reassemble the bounded endpoint-degree-three theorem package from the
full root-count forward direction and bundled predicate-restricted
x-subtraction cases. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current bounded endpoint-degree-three Liu package, assuming the isolated
forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three

/-- Current bounded endpoint-degree-three Liu package, assuming the isolated
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three

/-- Low-degree bounded Liu equivalence with the ordinary branch statement.
The reverse direction uses the endpoint-degree-three route after converting
ordinary branch data using the explicit degree bounds. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  ⟨hforward hf hg hsgn,
    theorem21RootCountBranchesToCompatible_of_natDegree_le_three
      hf hg hsgn hfdeg hgdeg⟩

/-- Low-degree bounded Liu equivalence from a predicate-restricted reverse
direction, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · exact hforward hf hg hsgn
  · intro hbranches
    exact hreverse hf hg hsgn
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- Low-degree bounded Liu equivalence from the branch-retaining
common-interleaver forward direction and a predicate-restricted reverse
direction. -/
theorem
    theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · intro hcompat
    exact theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
      (hforward hf hg hsgn hcompat)
  · intro hbranches
    exact hreverse hf hg hsgn
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- Low-degree bounded Liu equivalence from endpoint factor-return case
packages, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeEndpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)
    hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from endpoint factor-return case
packages and the root-count forward direction, with the ordinary branch
statement. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeEndpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from left endpoint factor-return case
packages, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeLeftCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
      hcases)
    hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from left endpoint factor-return case
packages and the root-count forward direction, with right cases supplied by
symmetry. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeLeftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from bundled predicate-restricted
x-subtraction cases, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeXSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)
    hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from bundled predicate-restricted
x-subtraction cases and the root-count forward direction, with the ordinary
branch statement. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeXSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases hf hg hsgn hfdeg hgdeg

/-- Reassemble the low-degree Liu theorem package from the full forward
direction and a predicate-restricted reverse direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  exact
    theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
      (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
        hforward)
      hreverse hf hg hsgn hfdeg hgdeg

/-- Reassemble the low-degree Liu theorem package from the branch-retaining
common-interleaver forward direction and a predicate-restricted reverse
direction. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  exact
    theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
      hforward hreverse hf hg hsgn hfdeg hgdeg

/-- Current low-degree Liu theorem package with the ordinary branch statement,
assuming the isolated forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three

/-- Current low-degree Liu theorem package with the ordinary branch statement,
assuming the isolated branch-retaining common-interleaver forward direction.
-/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three

/-- Current low-degree Liu theorem package from endpoint factor-return case
packages, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_endpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)

/-- Current low-degree Liu theorem package from endpoint factor-return case
packages and the root-count forward direction, with the ordinary branch
statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current low-degree Liu theorem package from left endpoint factor-return case
packages, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_leftCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
      hcases)

/-- Current low-degree Liu theorem package from left endpoint factor-return
case packages and the root-count forward direction, with right cases supplied
by symmetry. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_leftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases, with the ordinary branch statement.
-/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)

/-- Current low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases and the root-count forward direction,
with the ordinary branch statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and bounded nonconstant reverse
direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          f.natDegree ≠ 0 → g.natDegree ≠ 0 →
            theorem21RootCountBranchesEndpointLeThree f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact ⟨hforward hf hg hsgn hf_deg hg_deg,
    hreverse hf hg hsgn hf_deg hg_deg⟩

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant branch-retaining common-interleaver forward direction and
a predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesNonconstant_of_commonForward
      hforward)
    (fun hf hg hsgn hf_deg hg_deg hbranches =>
      hreverse hf hg hsgn hf_deg hg_deg hbranches)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and a predicate-restricted nonconstant
reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreverse

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and endpoint factor-return case
packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_endpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant root-count forward direction and endpoint factor-return
case packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and left endpoint factor-return case
packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_leftCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
      hcases)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant root-count forward direction and left endpoint
factor-return case packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_leftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and bundled predicate-restricted
x-subtraction cases. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_xSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant root-count forward direction and bundled
predicate-restricted x-subtraction cases. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant bounded endpoint-degree-three Liu package, assuming the
isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three

/-- Current nonconstant bounded endpoint-degree-three Liu package, assuming
the isolated nonconstant branch-retaining common-interleaver forward direction.
-/
theorem theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three

/-- Low-degree nonconstant bounded Liu equivalence with the ordinary branch
statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  ⟨hforward hf hg hsgn hfdeg_ne hgdeg_ne,
    theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_three
      hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le⟩

/-- Low-degree nonconstant bounded Liu equivalence from a
predicate-restricted nonconstant reverse direction, with the ordinary branch
statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · exact hforward hf hg hsgn hfdeg_ne hgdeg_ne
  · intro hbranches
    exact hreverse hf hg hsgn hfdeg_ne hgdeg_ne
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg_le hgdeg_le hbranches)

/-- Low-degree nonconstant bounded Liu equivalence from the nonconstant
branch-retaining common-interleaver forward direction and a
predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · intro hcompat
    exact theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
      (hforward hf hg hsgn hfdeg_ne hgdeg_ne hcompat)
  · intro hbranches
    exact hreverse hf hg hsgn hfdeg_ne hgdeg_ne
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg_le hgdeg_le hbranches)

/-- Low-degree nonconstant bounded Liu equivalence from endpoint factor-return
case packages, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeEndpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from endpoint factor-return
case packages and the nonconstant root-count forward direction, with the
ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeEndpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from left endpoint
factor-return case packages, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeLeftCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
      hcases)
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from left endpoint
factor-return case packages and the nonconstant root-count forward direction,
with right cases supplied by symmetry. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeLeftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from bundled
predicate-restricted x-subtraction cases, with the ordinary branch statement.
-/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeXSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from bundled
predicate-restricted x-subtraction cases and the nonconstant root-count forward
direction, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeXSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Reassemble the nonconstant low-degree Liu theorem package from the
nonconstant forward direction and a predicate-restricted nonconstant reverse
direction. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  exact
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
      (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
        hforward)
      hreverse hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Reassemble the nonconstant low-degree Liu theorem package from the
nonconstant branch-retaining common-interleaver forward direction and a
predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  exact
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
      hforward hreverse hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Current nonconstant low-degree Liu theorem package with the ordinary branch
statement, assuming the isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three

/-- Current nonconstant low-degree Liu theorem package with the ordinary branch
statement, assuming the isolated nonconstant branch-retaining common-interleaver
forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three

/-- Current nonconstant low-degree Liu theorem package from endpoint
factor-return case packages, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_endpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)

/-- Current nonconstant low-degree Liu theorem package from endpoint
factor-return case packages and the nonconstant root-count forward direction,
with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant low-degree Liu theorem package from left endpoint
factor-return case packages, with right cases supplied by symmetry. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_leftCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
      hcases)

/-- Current nonconstant low-degree Liu theorem package from left endpoint
factor-return case packages and the nonconstant root-count forward direction,
with right cases supplied by symmetry. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_leftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases, with the ordinary branch statement.
-/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_xSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)

/-- Current nonconstant low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases and the nonconstant root-count forward
direction, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Liu Theorem 2.1 follows from the isolated forward direction and a
predicate-`True` reverse direction. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_predicate_true
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranches_of_commonForward hforward)
    (theorem21RootCountBranchesToCompatible_of_predicate_true hreverse)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
a predicate-`True` reverse direction. -/
theorem theorem21CompatibleRootCount_of_forward_and_predicate_true
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_predicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreverse

/-- Liu Theorem 2.1 follows from the isolated forward root-count direction and
the deletion-pair factor-return principle. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_deletionPairCommonInterleaverIff
    (theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_factorReturn
      hforward hreturn)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
the deletion-pair factor-return principle. -/
theorem theorem21CompatibleRootCount_of_forward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- Liu Theorem 2.1 follows from the isolated forward direction and an
all-combinations factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnAllCombo
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
an all-combinations factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_forward_and_deletionPairFactorReturnAllCombo
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnAllCombo
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- Liu Theorem 2.1 follows from the isolated forward direction and
all-combinations factor-return degree cases. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
all-combinations factor-return degree cases. -/
theorem theorem21CompatibleRootCount_of_forward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_allComboDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Liu Theorem 2.1 follows from the isolated forward direction and left
all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_leftAllComboCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
left all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem theorem21CompatibleRootCount_of_forward_and_leftAllComboCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_leftAllComboCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Liu Theorem 2.1 follows from the isolated forward direction and a bundled
sign-normalized positive-split x-subtraction case package. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
a bundled sign-normalized positive-split x-subtraction case package. -/
theorem theorem21CompatibleRootCount_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Liu Theorem 2.1 follows from the isolated forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_xSubCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem theorem21CompatibleRootCount_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- Liu Theorem 2.1 follows from the isolated forward direction and a
predicate-`True` factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnPredicate_true
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true
      hreturn)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
a predicate-`True` factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_forward_and_deletionPairFactorReturnPredicate_true
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnPredicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- The deletion-pair factor-return principle also reduces the nonconstant
reverse direction of Liu Theorem 2.1. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_deletionPairFactorReturn
      hreturn)

/-- All-combinations factor-return proves the nonconstant reverse root-count
direction. -/
theorem
    theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturnAllCombo
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- All-combinations factor-return degree cases prove the nonconstant reverse
root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases prove the nonconstant
reverse root-count direction, with right cases supplied by symmetry. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_leftAllComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- A bundled sign-normalized positive-split x-subtraction case package proves
the nonconstant reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- Sign-normalized positive-split x-subtraction cases prove the nonconstant
reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and a predicate-`True` nonconstant reverse direction. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_predicate_true
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesNonconstant_of_commonForward
      hforward)
    (theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
      hreverse)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and a predicate-`True` nonconstant
reverse direction. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_predicate_true
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_predicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreverse

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and the deletion-pair factor-return principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_deletionPairCommonInterleaverIff
    (theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_factorReturn
      hforward hreturn)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and the deletion-pair factor-return
principle. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and an all-combinations factor-return principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturnAllCombo
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and an all-combinations factor-return
principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_deletionPairFactorReturnAllCombo
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturnAllCombo
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and all-combinations factor-return degree cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_allComboDegreeCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and all-combinations factor-return
degree cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_allComboDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and left all-combinations factor-return degree cases, with
right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_leftAllComboCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and left all-combinations
factor-return degree cases, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_leftAllComboCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_leftAllComboCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated forward
direction and a bundled sign-normalized positive-split x-subtraction case
package. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCasePackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and a bundled sign-normalized
positive-split x-subtraction case package. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and sign-normalized positive-split x-subtraction cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and sign-normalized positive-split
x-subtraction cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and a predicate-`True` factor-return principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_factorReturnPredicate_true
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true
      hreturn)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and a predicate-`True` factor-return
principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_deletionPairFactorReturnPredicate_true
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_factorReturnPredicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- Liu Corollary 2.2: compatible real-rooted polynomials with opposite leading
signs have degree gap at most two. -/
def corollary22DegreeDiffStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Nonconstant form of Liu Corollary 2.2. -/
def corollary22DegreeDiffNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
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

/-- Projection form of `corollary22DegreeDiffNonconstantStatement`. -/
theorem corollary22DegreeDiff_nonconstant
    (h : corollary22DegreeDiffNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hf_deg hg_deg hcompat

/-- Projection form of `corollary22DegreeDiffNatDegreeLeThreeStatement`. -/
theorem corollary22DegreeDiff_natDegree_le_three
    (h : corollary22DegreeDiffNatDegreeLeThreeStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hfdeg hgdeg hcompat

/-- Projection form of
`corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement`. -/
theorem corollary22DegreeDiff_natDegree_le_three_nonconstant
    (h : corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hf_deg hg_deg hfdeg hgdeg hcompat

/-- Low-degree Liu Corollary 2.2 follows from the checked low-degree
Theorem 2.1 package. -/
theorem corollary22DegreeDiffNatDegreeLeThree_of_theorem21NatDegreeLeThree
    (h : theorem21CompatibleRootCountNatDegreeLeThreeStatement) :
    corollary22DegreeDiffNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg hcompat
  exact natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
    ((h f g hf hg hsgn hfdeg hgdeg).1 hcompat)

/-- Nonconstant low-degree Liu Corollary 2.2 follows from the checked
nonconstant low-degree Theorem 2.1 package. -/
theorem
    corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_theorem21NatDegreeLeThree
    (h : theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement) :
    corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg hfdeg hgdeg hcompat
  exact natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
    ((h f g hf hg hsgn hf_deg hg_deg hfdeg hgdeg).1 hcompat)

/-- Low-degree Liu Corollary 2.2 follows from the isolated branch-retaining
common-interleaver forward direction. -/
theorem corollary22DegreeDiffNatDegreeLeThree_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    corollary22DegreeDiffNatDegreeLeThreeStatement :=
  corollary22DegreeDiffNatDegreeLeThree_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward hforward)

/-- Nonconstant low-degree Liu Corollary 2.2 follows from the isolated
nonconstant branch-retaining common-interleaver forward direction. -/
theorem corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement :=
  corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward
      hforward)

/-- Low-degree Liu Corollary 2.2 follows from the isolated forward direction of
Theorem 2.1. -/
theorem corollary22DegreeDiffNatDegreeLeThree_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    corollary22DegreeDiffNatDegreeLeThreeStatement :=
  corollary22DegreeDiffNatDegreeLeThree_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThree_of_forward hforward)

/-- Nonconstant low-degree Liu Corollary 2.2 follows from the isolated
nonconstant forward direction of Theorem 2.1. -/
theorem corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement :=
  corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward
      hforward)

/-- Liu Corollary 2.2 follows from the isolated branch-retaining
common-interleaver forward direction. -/
theorem corollary22DegreeDiff_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    corollary22DegreeDiffStatement :=
  fun _ _ hf hg hsgn hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
        (hforward hf hg hsgn hcompat))

/-- The nonconstant Liu Corollary 2.2 follows from the isolated nonconstant
branch-retaining common-interleaver forward direction. -/
theorem corollary22DegreeDiffNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    corollary22DegreeDiffNonconstantStatement :=
  fun _ _ hf hg hsgn hf_deg hg_deg hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
        (hforward hf hg hsgn hf_deg hg_deg hcompat))

/-- Liu Corollary 2.2 follows from the isolated forward direction of
Theorem 2.1. -/
theorem corollary22DegreeDiff_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    corollary22DegreeDiffStatement :=
  corollary22DegreeDiff_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)

/-- The nonconstant Liu Corollary 2.2 follows from the isolated nonconstant
forward direction of Theorem 2.1. -/
theorem corollary22DegreeDiffNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    corollary22DegreeDiffNonconstantStatement :=
  corollary22DegreeDiffNonconstant_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)

/-- Liu Corollary 2.2 follows from the Theorem 2.1 compatibility criterion. -/
theorem corollary22DegreeDiff_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    corollary22DegreeDiffStatement :=
  corollary22DegreeDiff_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)

/-- Nonconstant Liu Corollary 2.2 follows from the nonconstant Theorem 2.1
compatibility criterion. -/
theorem corollary22DegreeDiffNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    corollary22DegreeDiffNonconstantStatement :=
  corollary22DegreeDiffNonconstant_of_forward
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)

theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff (corollary22DegreeDiff_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

theorem
    natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff_nonconstant
    (corollary22DegreeDiffNonconstant_of_theorem21CompatibleRootCount h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Direct degree-gap consequence via the swapped branch projection of
Liu Theorem 2.1. -/
theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm hf hg hsgn
    (theorem21RootCountBranches_symm_of_compatible h hf hg hsgn hcompat)

/-- Nonconstant direct degree-gap consequence via the swapped branch
projection of Liu Theorem 2.1. -/
theorem
    natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm hf hg hsgn
    (theorem21RootCountBranches_symm_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg hcompat)

end LiuOppositeSigns
end RealRooted
