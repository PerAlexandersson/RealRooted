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
        (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
          P g.natDegree → Compatible f g) ∧
      (RightRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
          P f.natDegree → Compatible f g)

/-- Predicate-restricted factor-return principles transport along endpoint
predicate implications. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        Q) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      P :=
  fun hf hg hsgn =>
    ⟨fun hbranch hcommon hP =>
      (hQ hf hg hsgn).1 hbranch hcommon (hPQ _ hP),
     fun hbranch hcommon hP =>
      (hQ hf hg hsgn).2 hbranch hcommon (hPQ _ hP)⟩

/-- Predicate-restricted left factor-return degree cases. -/
def theorem21LeftFactorReturnDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted left factor-return degree cases.  Unlike
`theorem21LeftFactorReturnDegreeCasesPredicateStatement`, the predicate is
available in all three degree branches. -/
def theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreePredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreePredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P

/-- Predicate-restricted right factor-return degree cases. -/
def theorem21RightFactorReturnDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnSameDegreeStatement ∧
    theorem21RightFactorReturnSuccDegreeStatement ∧
      theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted right factor-return degree cases.  Unlike
`theorem21RightFactorReturnDegreeCasesPredicateStatement`, the predicate is
available in all three degree branches. -/
def theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnSameDegreePredicateStatement P ∧
    theorem21RightFactorReturnSuccDegreePredicateStatement P ∧
      theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Predicate-restricted left and right factor-return degree cases. -/
def theorem21FactorReturnPredicateDegreeCasesStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P ∧
        theorem21RightFactorReturnSameDegreeStatement ∧
          theorem21RightFactorReturnSuccDegreeStatement ∧
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

/-- Predicate-restricted left and right factor-return degree cases assemble
into the full six-case package. -/
theorem theorem21FactorReturnPredicateDegreeCases_of_leftRightCases
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnDegreeCasesPredicateStatement P)
    (hright : theorem21RightFactorReturnDegreeCasesPredicateStatement P) :
    theorem21FactorReturnPredicateDegreeCasesStatement P :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

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

/-- Left projection from a six-case predicate factor-return package. -/
theorem theorem21LeftFactorReturnDegreeCasesPredicate_of_factorCases
    {P : ℕ → Prop}
    (hcases : theorem21FactorReturnPredicateDegreeCasesStatement P) :
    theorem21LeftFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case predicate factor-return package. -/
theorem theorem21RightFactorReturnDegreeCasesPredicate_of_factorCases
    {P : ℕ → Prop}
    (hcases : theorem21FactorReturnPredicateDegreeCasesStatement P) :
    theorem21RightFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

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

/-- Predicate-restricted translated compatibility degree cases give
predicate-restricted original left factor-return degree cases. -/
theorem
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedCompatibleCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21LeftFactorReturnSameDegreePredicate_of_translatedCompatiblePredicate
      hcases.1,
    theorem21LeftFactorReturnSuccDegreePredicate_of_translatedCompatiblePredicate
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreePredicate_of_translatedCompatiblePredicate
      hcases.2.2⟩

/-- Predicate-restricted translated right-family degree cases give
predicate-restricted original left factor-return degree cases. -/
theorem
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedRightFamilyCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedCompatibleCasesPredicate
    (theorem21LeftFactorReturnTranslatedCompatibleCasesPredicate_of_rightFamilyCasesPredicate
      hcases)

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

/-- Predicate-restricted left factor-return case packages transport along
endpoint predicate implications. -/
theorem theorem21LeftFactorReturnDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21LeftFactorReturnDegreeCasesPredicateStatement Q) :
    theorem21LeftFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hQ.1, hQ.2.1,
    theorem21LeftFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Endpoint-predicate-restricted left factor-return case packages transport
along endpoint predicate implications. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement Q) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21LeftFactorReturnSameDegreePredicateStatement_of_imp
      hPQ hQ.1,
    theorem21LeftFactorReturnSuccDegreePredicateStatement_of_imp hPQ hQ.2.1,
    theorem21LeftFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Predicate-restricted right factor-return case packages transport along
endpoint predicate implications. -/
theorem theorem21RightFactorReturnDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnDegreeCasesPredicateStatement Q) :
    theorem21RightFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hQ.1, hQ.2.1,
    theorem21RightFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Endpoint-predicate-restricted right factor-return case packages transport
along endpoint predicate implications. -/
theorem theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement Q) :
    theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21RightFactorReturnSameDegreePredicateStatement_of_imp hPQ hQ.1,
    theorem21RightFactorReturnSuccDegreePredicateStatement_of_imp hPQ hQ.2.1,
    theorem21RightFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Predicate-restricted left/right factor-return case packages transport along
endpoint predicate implications. -/
theorem theorem21FactorReturnPredicateDegreeCasesStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21FactorReturnPredicateDegreeCasesStatement Q) :
    theorem21FactorReturnPredicateDegreeCasesStatement P :=
  theorem21FactorReturnPredicateDegreeCases_of_leftRightCases
    (theorem21LeftFactorReturnDegreeCasesPredicateStatement_of_imp hPQ
      (theorem21LeftFactorReturnDegreeCasesPredicate_of_factorCases hQ))
    (theorem21RightFactorReturnDegreeCasesPredicateStatement_of_imp hPQ
      (theorem21RightFactorReturnDegreeCasesPredicate_of_factorCases hQ))

/-- Endpoint-predicate-restricted left/right factor-return case packages
transport along endpoint predicate implications. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCasesStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21EndpointFactorReturnPredicateDegreeCasesStatement Q) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement P :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftRightCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
      hPQ
      (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
        hQ))
    (theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
      hPQ
      (theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
        hQ))

/-- Left endpoint cases through right degree two for all three restored-degree
factor-return branches. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_two :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
      (fun n => n ≤ 2) :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_two

/-- Left endpoint cases through right degree three for all three restored-degree
factor-return branches, modulo the normalized monic quartic/cubic arithmetic
leaf. -/
theorem
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
    (positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
      hmono)

/-- Left endpoint cases through right degree three for all three restored-degree
factor-return branches. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three_of_monic
    xSubQuarticCubicSplits

/-- Predicate-restricted left factor-return degree cases supply the matching
right cases by symmetry. -/
theorem theorem21RightFactorReturnDegreeCasesPredicate_of_leftCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnDegreeCasesPredicateStatement P) :
    theorem21RightFactorReturnDegreeCasesPredicateStatement P :=
  ⟨theorem21RightFactorReturnSameDegree_of_leftSameDegree hcases.1,
    theorem21RightFactorReturnSuccDegree_of_leftSuccDegree hcases.2.1,
    theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate hcases.2.2⟩

/-- Predicate-restricted left factor-return degree cases supply the matching
right cases by symmetry. -/
theorem theorem21FactorReturnPredicateDegreeCases_of_leftCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnDegreeCasesPredicateStatement P) :
    theorem21FactorReturnPredicateDegreeCasesStatement P :=
  theorem21FactorReturnPredicateDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnDegreeCasesPredicate_of_leftCases hcases)

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

/-- Full left/right endpoint cases through degree two, with right cases
supplied by symmetry from the named left endpoint package. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_endpoint_le_two :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement
      (fun n => n ≤ 2) :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_two

/-- Full left/right endpoint cases through degree three, modulo the normalized
monic quartic/cubic arithmetic leaf. -/
theorem
    theorem21EndpointFactorReturnPredicateDegreeCases_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement
      (fun n => n ≤ 3) :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Full left/right endpoint cases through degree three. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_endpoint_le_three :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement
      (fun n => n ≤ 3) :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three

/-- The predicate-restricted factor-return principle follows from its restored
degree cases. -/
theorem theorem21FactorReturnPredicate_of_degreeCases
    {P : ℕ → Prop}
    (hcases : theorem21FactorReturnPredicateDegreeCasesStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P := by
  let hleftCases :=
    theorem21LeftFactorReturnDegreeCasesPredicate_of_factorCases hcases
  let hrightCases :=
    theorem21RightFactorReturnDegreeCasesPredicate_of_factorCases hcases
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon hgdeg
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleftCases.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.2 hf hg hsgn hleft hdeg hcommon hgdeg
  · intro hright hcommon hfdeg
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hrightCases.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.2 hf hg hsgn hright hdeg hcommon hfdeg

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

/-- It is enough to prove the predicate-restricted left factor-return degree
cases; the right branch is symmetric. -/
theorem theorem21FactorReturnPredicate_of_leftCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnDegreeCasesPredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_degreeCases
    (theorem21FactorReturnPredicateDegreeCases_of_leftCases hcases)

/-- It is enough to prove endpoint-predicate-restricted left factor-return
degree cases; the right branch is symmetric. -/
theorem theorem21FactorReturnPredicate_of_leftEndpointCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_endpointDegreeCases
    (theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases hcases)

/-- Predicate-restricted translated compatibility degree cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_translatedCompatibleCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedCompatibleCasesPredicate
      hcases)

/-- Predicate-restricted translated right-family degree cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_translatedRightFamilyCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedRightFamilyCasesPredicate
      hcases)

/-- Predicate-restricted positive-split x-subtraction degree cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_xSubCasesPredicate
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasesPredicate
      hrightSucc hsame hleftSucc)

/-- Since the same-degree and left-successor x-subtraction cases are proved, the
predicate-restricted factor-return principle only needs the remaining
right-successor x-subtraction leaf. -/
theorem theorem21FactorReturnPredicate_of_rightSucc_xSubPredicate
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_xSubCasesPredicate
    hrightSucc (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate P)
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate

/-- The proved sign-normalized positive-split x-subtraction cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_xSub
    {P : ℕ → Prop} :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_xSubCasesPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate P)
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate

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

/-- A `P := True` restricted factor-return principle gives the unrestricted
factor-return principle. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    exact (hreturn hf hg hsgn).1 hleft hcommon trivial
  · intro hright hcommon
    exact (hreturn hf hg hsgn).2 hright hcommon trivial

/-- The unrestricted factor-return principle proves every predicate-restricted
factor-return principle by forgetting the endpoint predicate. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnPredicate_of_factorReturn
    {P : ℕ → Prop}
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon _hgdeg
    exact (hreturn hf hg hsgn).1 hleft hcommon
  · intro hright hcommon _hfdeg
    exact (hreturn hf hg hsgn).2 hright hcommon

/-- Predicate-`True` factor-return is equivalent to the ordinary factor-return
principle. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnPredicate_true_iff :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun _ => True) ↔
      theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  ⟨theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true,
    theorem21DeletionPairCommonInterleaverFactorReturnPredicate_of_factorReturn⟩

/-- Same-degree and succ-degree leaves plus a predicate-restricted two-degree
leaf give the predicate-restricted factor-return route. -/
theorem theorem21FactorReturnPredicate_of_sameSucc_and_twoPredicate
    {P : ℕ → Prop}
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreePredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftCases ⟨hsame, hsucc, htwo⟩

/-- Current low-endpoint factor-return route: the two-degree branch is proved
whenever the lower-degree endpoint has degree at most two. -/
theorem theorem21FactorReturnPredicate_of_sameSucc_and_endpoint_le_two
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 2) :=
  theorem21FactorReturnPredicate_of_sameSucc_and_twoPredicate
    (P := fun n => n ≤ 2) hsame hsucc
    theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_le_two

/-- Current low-endpoint factor-return route: all three left degree branches
are proved whenever the lower-degree endpoint has degree at most two. -/
theorem theorem21FactorReturnPredicate_of_endpoint_le_two :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 2) :=
  theorem21FactorReturnPredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_two

/-- Conditional low-endpoint factor-return route: once the normalized
quartic/cubic arithmetic terminal is proved, all three left degree branches are
available whenever the lower-degree endpoint has degree at most three. -/
theorem theorem21FactorReturnPredicate_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21FactorReturnPredicate_of_xSubCasePackage
    (positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
      hmono)

/-- Low-endpoint factor-return route: all three left degree branches are
available whenever the lower-degree endpoint has degree at most three. -/
theorem theorem21FactorReturnPredicate_of_endpoint_le_three :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21FactorReturnPredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three

end LiuOppositeSigns
end RealRooted
