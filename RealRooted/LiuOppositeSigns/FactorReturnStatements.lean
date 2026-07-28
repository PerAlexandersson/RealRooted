import RealRooted.LiuOppositeSigns.DeletionBranches

/-!
# Liu factor-return statement interface

This module contains the statement-level factor-return packages and the
left/right symmetry adapters used in the reverse direction of Liu Theorem 2.1.
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
end LiuOppositeSigns
end RealRooted
