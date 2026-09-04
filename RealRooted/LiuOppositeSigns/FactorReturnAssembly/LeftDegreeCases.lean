import RealRooted.LiuOppositeSigns.FactorReturnLeft
import RealRooted.LiuOppositeSigns.FactorReturnTwoDegree
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount

/-!
# Liu left factor-return degree cases

This module assembles the translated compatibility, right-family, and
x-subtraction routes for the three left deletion-branch degree cases.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The three left-branch factor-return cases.  The right-branch cases follow
by symmetry. -/
def theorem21LeftFactorReturnDegreeCasesStatement : Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreeStatement

/-- Translated compatibility targets for all three left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedCompatibleStatement ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatibleStatement ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement

/-- Translated right-family targets for all three left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyStatement ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyStatement ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement

/-- Sign-normalized positive-split x-subtraction cases for the three Liu
left-branch restored-degree cases. -/
def positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement : Prop :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement ∧
    positiveSplitSameDegreeTranslatedXSubRightFamilyStatement ∧
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement

/-- Predicate-restricted sign-normalized positive-split x-subtraction cases
for the three Liu left-branch restored-degree cases. -/
def positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement P ∧
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P ∧
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement P

/-- Predicate-restricted x-subtraction case packages transport along endpoint
predicate implications. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        Q) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      P :=
  ⟨positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
      hPQ hQ.1,
    positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
      hPQ hQ.2.1,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement_of_imp
      hPQ hQ.2.2⟩

/-- A predicate-`True` x-subtraction case package gives the corresponding
ordinary x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCases_of_predicate_true
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun _ => True)) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement :=
  ⟨positiveSplitTranslatedXSubRightFamilyRelation_of_predicate_true
      hcases.1,
    positiveSplitTranslatedXSubRightFamilyRelation_of_predicate_true
      hcases.2.1,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_predicate_true
      hcases.2.2⟩

/-- An ordinary x-subtraction case package gives the corresponding
predicate-`True` x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_true_of_cases
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun _ => True) :=
  ⟨positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hcases.1,
    positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hcases.2.1,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_true_of_xSub
      hcases.2.2⟩

/-- Unrestricted x-subtraction cases give the `P := True` x-subtraction case
package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_true_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun _ => True) :=
  positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_true_of_cases
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- Since the same-degree and left-successor x-subtraction cases are now proved,
the remaining unrestricted x-subtraction case package only needs the
right-successor leaf. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCases_of_rightSucc
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement :=
  ⟨hrightSucc, positiveSplitSameDegreeTranslatedXSubRightFamily,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily⟩

/-- The three sign-normalized positive-split x-subtraction cases are proved. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCases :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement :=
  positiveSplitTranslatedXSubRightFamilyDegreeCases_of_rightSucc
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily

/-- Since the same-degree and left-successor x-subtraction cases are now proved,
predicate-restricted x-subtraction case packages only need the right-successor
leaf. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_rightSucc
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P :=
  ⟨hrightSucc, positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate P,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate⟩

/-- The three sign-normalized positive-split x-subtraction cases are proved for
every endpoint predicate restriction. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate
    {P : ℕ → Prop} :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P :=
  positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_rightSucc
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate

/-- Endpoint cases through degree two as a bundled predicate-restricted
x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_two :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun n => n ≤ 2) :=
  positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_rightSucc
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two

/-- Endpoint cases through degree three as a bundled predicate-restricted
x-subtraction case package, modulo the normalized monic quartic/cubic leaf. -/
theorem
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  ⟨positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three,
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three,
    positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono⟩

/-- Endpoint cases through degree three as a bundled predicate-restricted
x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
    xSubQuarticCubicSplits

/-- Predicate-restricted translated compatibility targets for all three
left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
        P

/-- Predicate-restricted translated right-family targets for all three
left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        P

/-- Predicate-restricted translated compatibility case packages transport
along endpoint predicate implications. -/
theorem
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        Q) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
      P :=
  ⟨fun hf hg hsgn hleft hdeg hcommon hgdeg =>
      hQ.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg),
    fun hf hg hsgn hleft hdeg hcommon hgdeg =>
      hQ.2.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg),
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement_of_imp
      hPQ hQ.2.2⟩

/-- Predicate-restricted translated right-family case packages transport
along endpoint predicate implications. -/
theorem
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        Q) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
      P :=
  ⟨fun hf hg hsgn hleft hdeg hcommon hgdeg μ hμ =>
      hQ.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg) μ hμ,
    fun hf hg hsgn hleft hdeg hcommon hgdeg μ hμ =>
      hQ.2.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg) μ hμ,
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement_of_imp
      hPQ hQ.2.2⟩

/-- Left all-combinations factor-return degree cases give the corresponding
compatibility factor-return degree cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_allComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegree_of_allCombo hcases.1,
    theorem21LeftFactorReturnSuccDegree_of_allCombo hcases.2.1,
    theorem21LeftFactorReturnTwoDegree_of_allCombo hcases.2.2⟩

/-- Translated left factor-return degree cases give the corresponding original
compatibility factor-return degree cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_translatedCompatibleCases
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegree_of_translatedCompatible hcases.1,
    theorem21LeftFactorReturnSuccDegree_of_translatedCompatible hcases.2.1,
    theorem21LeftFactorReturnTwoDegree_of_translatedCompatible hcases.2.2⟩

/-- Translated right-family degree cases give translated compatibility degree
cases. -/
theorem theorem21LeftFactorReturnTranslatedCompatibleCases_of_rightFamilyCases
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_rightFamily
      hcases.1,
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_rightFamily
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightFamily
      hcases.2.2⟩

/-- Predicate-restricted translated right-family degree cases give
predicate-restricted translated compatibility degree cases. -/
theorem
    theorem21LeftFactorReturnTranslatedCompatibleCasesPredicate_of_rightFamilyCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
      P :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hcases.1,
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hcases.2.2⟩

/-- Translated right-family degree cases give the corresponding original
compatibility factor-return degree cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_translatedRightFamilyCases
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_translatedCompatibleCases
    (theorem21LeftFactorReturnTranslatedCompatibleCases_of_rightFamilyCases
      hcases)

/-- Positive-split x-subtraction degree cases give translated right-family
degree cases for the three Liu left branches.  The same-degree Liu branch uses
the right-successor terminal, the successor-degree branch uses the same-degree
terminal, and the two-degree branch uses the left-successor terminal. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyCases_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub
      hcases.1,
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub
      hcases.2.2⟩

/-- Positive-split x-subtraction degree cases give translated right-family
degree cases for the three Liu left branches.  The same-degree Liu branch uses
the right-successor terminal, the successor-degree branch uses the same-degree
terminal, and the two-degree branch uses the left-successor terminal. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyCases_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement :=
  theorem21LeftFactorReturnTranslatedRightFamilyCases_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- Sign-normalized positive-split x-subtraction cases give translated
compatibility cases for the three Liu left branches. -/
theorem theorem21LeftFactorReturnTranslatedCompatibleCases_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_xSub
      hrightSucc,
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_xSub hsame,
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_xSub
      hleftSucc⟩

/-- A bundled sign-normalized positive-split x-subtraction case package gives
translated compatibility cases for the three Liu left branches. -/
theorem theorem21LeftFactorReturnTranslatedCompatibleCases_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :=
  theorem21LeftFactorReturnTranslatedCompatibleCases_of_xSubCases
    hcases.1 hcases.2.1 hcases.2.2

/-- Sign-normalized positive-split x-subtraction cases give the three original
left-branch factor-return cases directly. -/
theorem theorem21LeftFactorReturnDegreeCases_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegree_of_xSub hrightSucc,
    theorem21LeftFactorReturnSuccDegree_of_xSub hsame,
    theorem21LeftFactorReturnTwoDegree_of_xSub hleftSucc⟩

/-- Since the same-degree and left-successor x-subtraction cases are proved, the
factor-return degree cases only need the remaining right-successor
x-subtraction leaf. -/
theorem theorem21LeftFactorReturnDegreeCases_of_rightSucc_xSub
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_xSubCases
    hrightSucc positiveSplitSameDegreeTranslatedXSubRightFamily
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily

/-- The proved sign-normalized positive-split x-subtraction cases give the three
original left-branch factor-return cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_xSub :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_xSubCases
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily
    positiveSplitSameDegreeTranslatedXSubRightFamily
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily

/-- A bundled sign-normalized positive-split x-subtraction case package gives
the three original left-branch factor-return cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_xSubCases
    hcases.1 hcases.2.1 hcases.2.2

/-- Predicate-restricted positive-split x-subtraction degree cases give
predicate-restricted translated right-family degree cases for the three Liu
left branches. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyCasesPredicate_of_xSubCasesPredicate
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
      P :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hrightSucc,
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsame,
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hleftSucc⟩

/-- Bundled predicate-restricted positive-split x-subtraction cases give
predicate-restricted translated right-family degree cases. -/
theorem
    theorem21LeftFactorReturnTranslatedRightFamilyCasesPredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
      P :=
  theorem21LeftFactorReturnTranslatedRightFamilyCasesPredicate_of_xSubCasesPredicate
    hcases.1 hcases.2.1 hcases.2.2

/-- Same-degree and succ-degree leaves plus the translated two-degree target
give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hsame, hsucc,
    theorem21LeftFactorReturnTwoDegree_of_translatedCompatible htwo⟩

/-- Same-degree and succ-degree leaves plus the translated right-family
two-degree target give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_rightFamily
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hsame, hsucc, theorem21LeftFactorReturnTwoDegree_of_rightFamily hright⟩

/-- Same-degree and succ-degree leaves plus the positive-split subtraction
family leaf give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_xSub
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_rightFamily hsame hsucc
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub hsub)

end LiuOppositeSigns
end RealRooted
