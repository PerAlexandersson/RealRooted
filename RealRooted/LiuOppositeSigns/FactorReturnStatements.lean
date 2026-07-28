import RealRooted.LiuOppositeSigns.DeletionBranches

/-!
# Liu factor-return statement interface

This module contains the statement-level factor-return packages, target
aliases, and left/right symmetry adapters used in the reverse direction of Liu
Theorem 2.1.
The proof-heavy degree branches and final theorem assembly remain in
`RealRooted.LiuOppositeSignsTheorem`.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The remaining factor-return principle for the reverse direction of Liu
Theorem 2.1.  It says that once the selected deletion pair has a common
right interleaver, the deleted largest linear factor can be put back to recover
compatibility of the original opposite-leading-sign pair. -/
def theorem21DeletionPairCommonInterleaverFactorReturnStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      (LeftRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
          Compatible f g) ∧
      (RightRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
          Compatible f g)

/-- The factor-return principle proves the branch-retaining
common-interleaver reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverBranchesToCompatible_of_factorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  rcases hbranches with ⟨r, s, hleft | hright⟩
  · exact (hreturn hf hg hsgn).1 hleft.1 hleft.2
  · exact (hreturn hf hg hsgn).2 hright.1 hright.2

/-- The factor-return principle proves the nonconstant branch-retaining
common-interleaver reverse direction. -/
theorem
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstant_of_factorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstant_of_reverse
    (theorem21DeletionPairCommonInterleaverBranchesToCompatible_of_factorReturn
      hreturn)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and factor-return principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_factorReturn
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21CompatibleDeletionPairCommonInterleaverBranches_of_forward_and_reverse
    hforward
    (theorem21DeletionPairCommonInterleaverBranchesToCompatible_of_factorReturn
      hreturn)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and factor-return
principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_factorReturn
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_factorReturn
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and
factor-return principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_factorReturn
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstant_of_forward_and_reverse
    hforward
    (theorem21DeletionPairCommonInterleaverBranchesToCompatibleNonconstant_of_factorReturn
      hreturn)

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
factor-return principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_factorReturn
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_factorReturn
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- Stronger all-real-combination version of the factor-return principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement :
    Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      (LeftRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
          AllComboRealRooted f g) ∧
      (RightRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
          AllComboRealRooted f g)

/-- The all-real-combination factor-return target implies the existing
compatibility factor-return target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    exact Compatible.of_allComboRealRooted
      ((hreturn hf hg hsgn).1 hleft hcommon)
  · intro hright hcommon
    exact Compatible.of_allComboRealRooted
      ((hreturn hf hg hsgn).2 hright hcommon)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and all-combinations factor-return
principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allCombo
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_factorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and all-combinations
factor-return principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_allCombo
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allCombo
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and
all-combinations factor-return principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allCombo
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_factorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
all-combinations factor-return principle. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_allCombo
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allCombo
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- Swap the common-right-interleaver witness in a right deletion pair. -/
theorem rightDeletionPairCommonInterleaver_symm {f g : ℝ[X]} {s : ℝ}
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) :
    ∃ k : ℝ[X], Prec (deleteRootFactor g s) k ∧ Prec f k := by
  rcases hcommon with ⟨k, hfk, hgk⟩
  exact ⟨k, hgk, hfk⟩

/-- Left-branch all-combinations factor-return target for an arbitrary endpoint
degree relation. -/
def theorem21LeftFactorReturnAllComboRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            AllComboRealRooted f g

/-- Same-degree left-branch all-combinations factor-return target. -/
def theorem21LeftFactorReturnSameDegreeAllComboStatement : Prop :=
  theorem21LeftFactorReturnAllComboRelationStatement
    (fun m n => m = n)

/-- Succ-degree left-branch all-combinations factor-return target. -/
def theorem21LeftFactorReturnSuccDegreeAllComboStatement : Prop :=
  theorem21LeftFactorReturnAllComboRelationStatement
    (fun m n => m = n + 1)

/-- Two-degree-gap left-branch all-combinations factor-return target. -/
def theorem21LeftFactorReturnTwoDegreeAllComboStatement : Prop :=
  theorem21LeftFactorReturnAllComboRelationStatement
    (fun m n => m = n + 2)

/-- The three left-branch all-combinations factor-return cases.  The right
branch follows by symmetry. -/
def theorem21LeftFactorReturnAllComboDegreeCasesStatement : Prop :=
  theorem21LeftFactorReturnSameDegreeAllComboStatement ∧
    theorem21LeftFactorReturnSuccDegreeAllComboStatement ∧
      theorem21LeftFactorReturnTwoDegreeAllComboStatement

/-- Right-branch all-combinations factor-return target for an arbitrary endpoint
degree relation.  The relation is evaluated as `R g.natDegree f.natDegree`,
matching the right branch where `g` is the endpoint with the deleted root. -/
def theorem21RightFactorReturnAllComboRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        R g.natDegree f.natDegree →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            AllComboRealRooted f g

/-- Same-degree right-branch all-combinations factor-return target. -/
def theorem21RightFactorReturnSameDegreeAllComboStatement : Prop :=
  theorem21RightFactorReturnAllComboRelationStatement
    (fun m n => m = n)

/-- Succ-degree right-branch all-combinations factor-return target. -/
def theorem21RightFactorReturnSuccDegreeAllComboStatement : Prop :=
  theorem21RightFactorReturnAllComboRelationStatement
    (fun m n => m = n + 1)

/-- Two-degree-gap right-branch all-combinations factor-return target. -/
def theorem21RightFactorReturnTwoDegreeAllComboStatement : Prop :=
  theorem21RightFactorReturnAllComboRelationStatement
    (fun m n => m = n + 2)

/-- The three right-branch all-combinations factor-return cases. -/
def theorem21RightFactorReturnAllComboDegreeCasesStatement : Prop :=
  theorem21RightFactorReturnSameDegreeAllComboStatement ∧
    theorem21RightFactorReturnSuccDegreeAllComboStatement ∧
      theorem21RightFactorReturnTwoDegreeAllComboStatement

/-- General symmetry bridge from a left-branch all-combinations factor-return
theorem to the matching right-branch theorem with the degree relation
reversed. -/
theorem theorem21RightFactorReturnAllCombo_of_leftDegreeRelation
    {R : ℕ → ℕ → Prop}
    (hleft : theorem21LeftFactorReturnAllComboRelationStatement R)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : R g.natDegree f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) :
    AllComboRealRooted f g :=
  allComboRealRooted_comm <|
    hleft (f := g) (g := f) (r := s) (s := r)
      hg hf hsgn.symm hright.toLeftBranch_symm hdeg
      (rightDeletionPairCommonInterleaver_symm hcommon)

/-- A left all-combinations relation theorem gives the matching right-branch
relation theorem by symmetry. -/
theorem theorem21RightFactorReturnAllComboRelation_of_leftRelation
    {R : ℕ → ℕ → Prop}
    (hleft : theorem21LeftFactorReturnAllComboRelationStatement R) :
    theorem21RightFactorReturnAllComboRelationStatement R := by
  intro f g r s hf hg hsgn hright hdeg hcommon
  exact theorem21RightFactorReturnAllCombo_of_leftDegreeRelation
    hleft hf hg hsgn hright hdeg hcommon

/-- The right same-degree all-combinations factor-return case follows from
the left same-degree case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSameDegreeAllCombo_of_leftSameDegree
    (hleft : theorem21LeftFactorReturnSameDegreeAllComboStatement) :
    theorem21RightFactorReturnSameDegreeAllComboStatement :=
  theorem21RightFactorReturnAllComboRelation_of_leftRelation
    (R := fun m n => m = n) hleft

/-- The right successor-degree all-combinations factor-return case follows
from the left successor-degree case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSuccDegreeAllCombo_of_leftSuccDegree
    (hleft : theorem21LeftFactorReturnSuccDegreeAllComboStatement) :
    theorem21RightFactorReturnSuccDegreeAllComboStatement :=
  theorem21RightFactorReturnAllComboRelation_of_leftRelation
    (R := fun m n => m = n + 1) hleft

/-- The right two-degree-gap all-combinations factor-return case follows
from the left two-degree-gap case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnTwoDegreeAllCombo_of_leftTwoDegree
    (hleft : theorem21LeftFactorReturnTwoDegreeAllComboStatement) :
    theorem21RightFactorReturnTwoDegreeAllComboStatement :=
  theorem21RightFactorReturnAllComboRelation_of_leftRelation
    (R := fun m n => m = n + 2) hleft

/-- Left all-combinations factor-return degree cases give the matching right
degree cases by symmetry. -/
theorem theorem21RightFactorReturnAllComboDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21RightFactorReturnAllComboDegreeCasesStatement :=
  ⟨theorem21RightFactorReturnSameDegreeAllCombo_of_leftSameDegree hcases.1,
    theorem21RightFactorReturnSuccDegreeAllCombo_of_leftSuccDegree hcases.2.1,
    theorem21RightFactorReturnTwoDegreeAllCombo_of_leftTwoDegree hcases.2.2⟩

/-- Degree-case split needed to prove the all-combinations factor-return
principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeAllComboStatement ∧
    theorem21LeftFactorReturnSuccDegreeAllComboStatement ∧
      theorem21LeftFactorReturnTwoDegreeAllComboStatement ∧
        theorem21RightFactorReturnSameDegreeAllComboStatement ∧
          theorem21RightFactorReturnSuccDegreeAllComboStatement ∧
            theorem21RightFactorReturnTwoDegreeAllComboStatement

/-- Left and right all-combinations factor-return degree cases assemble into
the full six-case package. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCases_of_leftRightCases
    (hleft : theorem21LeftFactorReturnAllComboDegreeCasesStatement)
    (hright : theorem21RightFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

/-- Left projection from a six-case all-combinations factor-return package. -/
theorem theorem21LeftFactorReturnAllComboDegreeCases_of_allComboFactorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21LeftFactorReturnAllComboDegreeCasesStatement :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case all-combinations factor-return package. -/
theorem theorem21RightFactorReturnAllComboDegreeCases_of_allComboFactorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21RightFactorReturnAllComboDegreeCasesStatement :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

/-- Left all-combinations factor-return degree cases supply all six left/right
cases by symmetry. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnAllComboDegreeCases_of_leftCases hcases)

/-- The explicit all-combinations factor-return principle follows from its
six restored-degree cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement := by
  let hleftCases :=
    theorem21LeftFactorReturnAllComboDegreeCases_of_allComboFactorCases hcases
  let hrightCases :=
    theorem21RightFactorReturnAllComboDegreeCases_of_allComboFactorCases hcases
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleftCases.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.2 hf hg hsgn hleft hdeg hcommon
  · intro hright hcommon
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hrightCases.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.2 hf hg hsgn hright hdeg hcommon

/-- It is enough to prove the left-branch all-combinations factor-return
cases; the right branch is symmetric. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_leftCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCases_of_leftCases
      hcases)

/-- Left-branch factor-return target for an arbitrary endpoint degree
relation. -/
def theorem21LeftFactorReturnRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            Compatible f g

/-- Predicate-restricted left-branch factor-return target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions on
`g.natDegree`. -/
def theorem21LeftFactorReturnPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            P g.natDegree → Compatible f g

/-- Predicate-restricted left factor-return relation targets transport along
endpoint predicate implications. -/
theorem theorem21LeftFactorReturnPredicateRelationStatement_of_imp
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21LeftFactorReturnPredicateRelationStatement R Q) :
    theorem21LeftFactorReturnPredicateRelationStatement R P := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact hQ hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg)

/-- The unrestricted left factor-return relation target is the `P := True`
case of the predicate-restricted relation target. -/
theorem theorem21LeftFactorReturnPredicateRelation_true_of_relation
    {R : ℕ → ℕ → Prop}
    (hreturn : theorem21LeftFactorReturnRelationStatement R) :
    theorem21LeftFactorReturnPredicateRelationStatement R
      (fun _ => True) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon _
  exact hreturn hf hg hsgn hleft hdeg hcommon

/-- A `P := True` left factor-return predicate relation target gives the
unrestricted relation target. -/
theorem theorem21LeftFactorReturnRelation_of_predicate_true
    {R : ℕ → ℕ → Prop}
    (hreturn :
      theorem21LeftFactorReturnPredicateRelationStatement R
        (fun _ => True)) :
    theorem21LeftFactorReturnRelationStatement R := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact hreturn hf hg hsgn hleft hdeg hcommon trivial

/-- Same-degree left-branch factor-return target. -/
def theorem21LeftFactorReturnSameDegreeStatement : Prop :=
  theorem21LeftFactorReturnRelationStatement
    (fun m n => m = n)

/-- Succ-degree left-branch factor-return target. -/
def theorem21LeftFactorReturnSuccDegreeStatement : Prop :=
  theorem21LeftFactorReturnRelationStatement
    (fun m n => m = n + 1)

/-- Predicate-restricted same-degree left-branch factor-return target.
The predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnSameDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnPredicateRelationStatement
    (fun m n => m = n) P

/-- Predicate-restricted successor-degree left-branch factor-return target.
The predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnSuccDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnPredicateRelationStatement
    (fun m n => m = n + 1) P

/-- Two-degree-gap left-branch factor-return target. -/
def theorem21LeftFactorReturnTwoDegreeStatement : Prop :=
  theorem21LeftFactorReturnRelationStatement
    (fun m n => m = n + 2)

/-- Predicate-restricted two-degree-gap left-branch factor-return target.
The predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnTwoDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnPredicateRelationStatement
    (fun m n => m = n + 2) P

/-- Predicate-restricted original two-degree factor-return targets transport
along endpoint predicate implications. -/
theorem theorem21LeftFactorReturnTwoDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21LeftFactorReturnTwoDegreePredicateStatement Q) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement P :=
  theorem21LeftFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n + 2) hPQ hQ

/-- Predicate-restricted same-degree factor-return targets transport along
endpoint predicate implications. -/
theorem theorem21LeftFactorReturnSameDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21LeftFactorReturnSameDegreePredicateStatement Q) :
    theorem21LeftFactorReturnSameDegreePredicateStatement P :=
  theorem21LeftFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n) hPQ hQ

/-- Predicate-restricted successor-degree factor-return targets transport
along endpoint predicate implications. -/
theorem theorem21LeftFactorReturnSuccDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21LeftFactorReturnSuccDegreePredicateStatement Q) :
    theorem21LeftFactorReturnSuccDegreePredicateStatement P :=
  theorem21LeftFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n + 1) hPQ hQ

/-- A left all-combinations factor-return leaf for any degree relation gives
the corresponding compatibility factor-return leaf. -/
theorem theorem21LeftFactorReturn_of_allComboRelation
    {R : ℕ → ℕ → Prop}
    (hleft : theorem21LeftFactorReturnAllComboRelationStatement R) :
    theorem21LeftFactorReturnRelationStatement R := by
  intro f g r s hf hg hsgn hbranch hdeg hcommon
  exact Compatible.of_allComboRealRooted
    (hleft hf hg hsgn hbranch hdeg hcommon)

/-- A same-degree all-combinations left leaf gives the corresponding
compatibility leaf. -/
theorem theorem21LeftFactorReturnSameDegree_of_allCombo
    (hleft : theorem21LeftFactorReturnSameDegreeAllComboStatement) :
    theorem21LeftFactorReturnSameDegreeStatement :=
  theorem21LeftFactorReturn_of_allComboRelation
    (R := fun m n => m = n) hleft

/-- A successor-degree all-combinations left leaf gives the corresponding
compatibility leaf. -/
theorem theorem21LeftFactorReturnSuccDegree_of_allCombo
    (hleft : theorem21LeftFactorReturnSuccDegreeAllComboStatement) :
    theorem21LeftFactorReturnSuccDegreeStatement :=
  theorem21LeftFactorReturn_of_allComboRelation
    (R := fun m n => m = n + 1) hleft

/-- A two-degree-gap all-combinations left leaf gives the corresponding
compatibility leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_allCombo
    (hleft : theorem21LeftFactorReturnTwoDegreeAllComboStatement) :
    theorem21LeftFactorReturnTwoDegreeStatement :=
  theorem21LeftFactorReturn_of_allComboRelation
    (R := fun m n => m = n + 2) hleft

/-- Translated compatibility target for a Liu left-branch factor-return route
with an arbitrary endpoint degree relation.  This isolates the common final
step of restoring the deleted largest root after translating it to the origin. -/
def theorem21LeftFactorReturnTranslatedCompatibleRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            Compatible
              (X * (deleteRootFactor f r).comp (X + C r))
              (g.comp (X + C r))

/-- Predicate-restricted translated compatibility target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions on
`g.natDegree`. -/
def theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            P g.natDegree →
              Compatible
                (X * (deleteRootFactor f r).comp (X + C r))
                (g.comp (X + C r))

/-- Predicate-restricted translated compatibility relation targets transport
along endpoint predicate implications. -/
theorem
    theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement_of_imp
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
        R Q) :
    theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
      R P := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact hQ hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg)

/-- The unrestricted translated compatibility relation target is the
`P := True` case of the predicate-restricted relation target. -/
theorem theorem21LeftFactorReturnTranslatedCompatiblePredicateRelation_true_of_relation
    {R : ℕ → ℕ → Prop}
    (htranslated :
      theorem21LeftFactorReturnTranslatedCompatibleRelationStatement R) :
    theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
      R (fun _ => True) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon _
  exact htranslated hf hg hsgn hleft hdeg hcommon

/-- A `P := True` translated compatibility predicate relation target gives the
unrestricted translated compatibility relation target. -/
theorem theorem21LeftFactorReturnTranslatedCompatibleRelation_of_predicate_true
    {R : ℕ → ℕ → Prop}
    (htranslated :
      theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
        R (fun _ => True)) :
    theorem21LeftFactorReturnTranslatedCompatibleRelationStatement R := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact htranslated hf hg hsgn hleft hdeg hcommon trivial

/-- Pointwise translated compatibility descent for a Liu left-branch
factor-return route. -/
theorem theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible
    {f g : ℝ[X]} {r s : ℝ}
    (hleft : LeftRootCountBranch f g r s)
    (htranslated :
      Compatible
        (X * (deleteRootFactor f r).comp (X + C r))
        (g.comp (X + C r))) :
    Compatible f g :=
  hleft.compatible_of_translated_restore htranslated

/-- A translated compatibility proof for any degree relation gives the
corresponding original left-branch factor-return proof.  This is the common
descent step behind the same-, successor-, and two-degree wrappers. -/
theorem theorem21LeftFactorReturn_of_translatedCompatibleRelation
    {R : ℕ → ℕ → Prop}
    (htranslated :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                Compatible
                  (X * (deleteRootFactor f r).comp (X + C r))
                  (g.comp (X + C r))) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              Compatible f g := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft
    (htranslated hf hg hsgn hleft hdeg hcommon)

/-- Predicate-restricted translated compatibility targets give the
corresponding predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnPredicate_of_translatedCompatibleRelation
    {R : ℕ → ℕ → Prop} {P : ℕ → Prop}
    (htranslated :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                P g.natDegree →
                  Compatible
                    (X * (deleteRootFactor f r).comp (X + C r))
                    (g.comp (X + C r))) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              P g.natDegree → Compatible f g := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft
    (htranslated hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Translated same-degree left-branch factor-return target. -/
def theorem21LeftFactorReturnSameDegreeTranslatedCompatibleStatement :
    Prop :=
  theorem21LeftFactorReturnTranslatedCompatibleRelationStatement
    (fun m n => m = n)

/-- Translated successor-degree left-branch factor-return target. -/
def theorem21LeftFactorReturnSuccDegreeTranslatedCompatibleStatement :
    Prop :=
  theorem21LeftFactorReturnTranslatedCompatibleRelationStatement
    (fun m n => m = n + 1)

/-- Predicate-restricted translated same-degree left-branch factor-return
target.  The predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
    (fun m n => m = n) P

/-- Predicate-restricted translated successor-degree left-branch factor-return
target.  The predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
    (fun m n => m = n + 1) P

/-- Translated two-degree left-branch factor-return target.  This keeps the
original sign of `g` and asks only for compatibility, avoiding the false
all-combinations strengthening. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement : Prop :=
  theorem21LeftFactorReturnTranslatedCompatibleRelationStatement
    (fun m n => m = n + 2)

/-- Predicate-restricted translated two-degree compatibility target.  The
predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
    (fun m n => m = n + 2) P

/-- Predicate-restricted translated compatibility targets transport along
endpoint predicate implications. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
        Q) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      P :=
  theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement_of_imp
    (R := fun m n => m = n + 2) hPQ hQ

/-- One-parameter positive right-pencil version of a translated Liu
left-branch target for an arbitrary endpoint degree relation. -/
def theorem21LeftFactorReturnTranslatedRightFamilyRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            ∀ μ : ℝ, 0 < μ →
              (X * (deleteRootFactor f r).comp (X + C r) +
                  C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted translated right-family target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions such
as fixed right degree or a low-degree bound. -/
def theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            P g.natDegree →
              ∀ μ : ℝ, 0 < μ →
                (X * (deleteRootFactor f r).comp (X + C r) +
                    C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted translated right-family relation targets transport
along endpoint predicate implications. -/
theorem
    theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement_of_imp
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
        R Q) :
    theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
      R P := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg μ hμ
  exact hQ hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg) μ hμ

/-- The unrestricted translated right-family relation target is the `P := True`
case of the predicate-restricted relation target. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelation_true_of_relation
    {R : ℕ → ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnTranslatedRightFamilyRelationStatement R) :
    theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
      R (fun _ => True) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon _ μ hμ
  exact hright hf hg hsgn hleft hdeg hcommon μ hμ

/-- A `P := True` translated right-family predicate relation target gives the
unrestricted translated right-family relation target. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyRelation_of_predicate_true
    {R : ℕ → ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
        R (fun _ => True)) :
    theorem21LeftFactorReturnTranslatedRightFamilyRelationStatement R := by
  intro f g r s hf hg hsgn hleft hdeg hcommon μ hμ
  exact hright hf hg hsgn hleft hdeg hcommon trivial μ hμ

/-- Pointwise right-family form of a translated left-branch Liu compatibility
target.  This separates endpoint splitting and coefficient scaling from the
degree-specific right-family leaves. -/
theorem theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hright : ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  have hdelete_rr :
      deleteRootFactor f r ≠ 0 ∧ (deleteRootFactor f r).Splits :=
    hleft.delete_ne_zero_and_splits hsgn.left_ne_zero hf
  have hdelete_shift_rr :
      (deleteRootFactor f r).comp (X + C r) ≠ 0 ∧
        ((deleteRootFactor f r).comp (X + C r)).Splits :=
    isRealRooted_comp_X_add_C hdelete_rr.1 hdelete_rr.2 r
  have hrestored_split :
      (X * (deleteRootFactor f r).comp (X + C r)).Splits :=
    (isRealRooted_X_mul hdelete_shift_rr.1 hdelete_shift_rr.2).2
  have hg_shift_split : (g.comp (X + C r)).Splits :=
    (isRealRooted_comp_X_add_C hsgn.right_ne_zero hg r).2
  exact Compatible.of_splits_of_pos_right_family hrestored_split hg_shift_split
    hright

/-- A translated positive right-family leaf for any degree relation gives the
corresponding translated compatibility target by scaling an arbitrary
nonnegative linear combination. -/
theorem theorem21LeftFactorReturnTranslatedCompatible_of_rightFamilyRelation
    {R : ℕ → ℕ → Prop}
    (hright :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                ∀ μ : ℝ, 0 < μ →
                  (X * (deleteRootFactor f r).comp (X + C r) +
                      C μ * g.comp (X + C r)).Splits) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              Compatible
                (X * (deleteRootFactor f r).comp (X + C r))
                (g.comp (X + C r)) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft (hright hf hg hsgn hleft hdeg hcommon)

/-- Predicate-restricted translated positive right-family leaves for any
degree relation give the corresponding pointwise translated compatibility
target. -/
theorem theorem21LeftFactorReturnTranslatedCompatible_of_rightPredicateRelation
    {R : ℕ → ℕ → Prop} {P : ℕ → Prop}
    (hright :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                P g.natDegree →
                  ∀ μ : ℝ, 0 < μ →
                    (X * (deleteRootFactor f r).comp (X + C r) +
                        C μ * g.comp (X + C r)).Splits) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              P g.natDegree →
                Compatible
                  (X * (deleteRootFactor f r).comp (X + C r))
                  (g.comp (X + C r)) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft (hright hf hg hsgn hleft hdeg hcommon hgdeg)

/-- One-parameter positive right-pencil version of the translated same-degree
target.  After deleting the largest left root, the sign-normalized deletion
pair has the right endpoint one degree higher. -/
def theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyStatement :
    Prop :=
  theorem21LeftFactorReturnTranslatedRightFamilyRelationStatement
    (fun m n => m = n)

/-- One-parameter positive right-pencil version of the translated
successor-degree target.  After deleting the largest left root, the
sign-normalized deletion pair has equal endpoint degrees. -/
def theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyStatement :
    Prop :=
  theorem21LeftFactorReturnTranslatedRightFamilyRelationStatement
    (fun m n => m = n + 1)

/-- Predicate-restricted translated same-degree right-family target. -/
def theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
    (fun m n => m = n) P

/-- Predicate-restricted translated successor-degree right-family target. -/
def theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
    (fun m n => m = n + 1) P

/-- One-parameter positive right-pencil version of the translated two-degree
target.  This is the remaining genuinely mathematical leaf after endpoint
splitting and coefficient scaling have been separated out. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement : Prop :=
  theorem21LeftFactorReturnTranslatedRightFamilyRelationStatement
    (fun m n => m = n + 2)

/-- Predicate-restricted form of the translated two-degree right-family
target.  The predicate records endpoint side conditions such as `natDegree = 0`,
`natDegree = 1`, or `natDegree ≤ 1`. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
    (fun m n => m = n + 2) P

/-- Predicate-restricted translated right-family targets transport along
endpoint predicate implications. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        Q) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      P :=
  theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement_of_imp
    (R := fun m n => m = n + 2) hPQ hQ

end LiuOppositeSigns
end RealRooted
