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

/-- Left all-combinations factor-return degree cases give the corresponding
compatibility factor-return degree cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_allComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegree_of_allCombo hcases.1,
    theorem21LeftFactorReturnSuccDegree_of_allCombo hcases.2.1,
    theorem21LeftFactorReturnTwoDegree_of_allCombo hcases.2.2⟩

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

/-- A bundled sign-normalized positive-split x-subtraction case package gives
the three original left-branch factor-return cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_xSubCases
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
