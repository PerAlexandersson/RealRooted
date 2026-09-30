import RealRooted.LiuOppositeSigns.FactorReturnAssembly.RightDegreeCases

/-!
# Liu predicate-restricted factor-return degree cases

This module combines the left and right degree cases under predicates on the
lower-degree endpoint and packages the low-degree x-subtraction routes.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Predicate-restricted factor-return principle for Liu deletion branches.
The predicate is imposed on the lower-degree endpoint only in the two-degree
branch: on `g.natDegree` in a left branch and on `f.natDegree` in a right
branch. -/
def theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
    (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      (LeftRootCountBranch f g r s →
        (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
          P g.natDegree → Compatible f g) ∧
      (RightRootCountBranch f g r s →
        (∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl (deleteRootFactor g s) k) →
          P f.natDegree → Compatible f g)

/-- Endpoint-predicate-restricted left factor-return degree cases: the
predicate is available in all three degree branches. -/
def theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreePredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreePredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted right factor-return degree cases: the
predicate is available in all three degree branches. -/
def theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnSameDegreePredicateStatement P ∧
    theorem21RightFactorReturnSuccDegreePredicateStatement P ∧
      theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted left and right factor-return degree cases. -/
def theorem21EndpointFactorReturnPredicateDegreeCasesStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreePredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreePredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P ∧
        theorem21RightFactorReturnSameDegreePredicateStatement P ∧
          theorem21RightFactorReturnSuccDegreePredicateStatement P ∧
            theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted left and right factor-return degree cases
assemble into the full six-case package. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_leftRightCases
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P)
    (hright :
      theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement P :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

/-- Left projection from a six-case endpoint-predicate factor-return package. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
    {P : ℕ → Prop}
    (hcases : theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case endpoint-predicate factor-return package. -/
theorem theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
    {P : ℕ → Prop}
    (hcases : theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

/-- Predicate-restricted positive-split x-subtraction degree cases give
predicate-restricted original left factor-return degree cases. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasesPredicate
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate hrightSucc,
    theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate hsame,
    theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate hleftSucc⟩

/-- Bundled predicate-restricted positive-split x-subtraction cases give
predicate-restricted original left factor-return degree cases. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasesPredicate
    hcases.1 hcases.2.1 hcases.2.2

/-- Endpoint-predicate-restricted left factor-return degree cases supply the
matching right cases by symmetry. -/
theorem theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_leftCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate hcases.1,
    theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate hcases.2.1,
    theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate hcases.2.2⟩

/-- Endpoint-predicate-restricted left factor-return degree cases supply the
matching right cases by symmetry. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement P :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_leftCases
      hcases)

/-- The predicate-restricted factor-return principle follows from endpoint-
predicate-restricted restored degree cases. -/
theorem theorem21FactorReturnPredicate_of_endpointDegreeCases
    {P : ℕ → Prop}
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P := by
  let hleftCases :=
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
      hcases
  let hrightCases :=
    theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
      hcases
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon hgdeg
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleftCases.1 hf hg hsgn hleft hdeg hcommon hgdeg
    · exact hleftCases.2.1 hf hg hsgn hleft hdeg hcommon hgdeg
    · exact hleftCases.2.2 hf hg hsgn hleft hdeg hcommon hgdeg
  · intro hright hcommon hfdeg
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hrightCases.1 hf hg hsgn hright hdeg hcommon hfdeg
    · exact hrightCases.2.1 hf hg hsgn hright hdeg hcommon hfdeg
    · exact hrightCases.2.2 hf hg hsgn hright hdeg hcommon hfdeg

/-- It is enough to prove endpoint-predicate-restricted left factor-return
degree cases; the right branch is symmetric. -/
theorem theorem21FactorReturnPredicate_of_leftEndpointCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_endpointDegreeCases
    (theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases hcases)

/-- Bundled predicate-restricted positive-split x-subtraction cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
      hcases)

end LiuOppositeSigns
end RealRooted
