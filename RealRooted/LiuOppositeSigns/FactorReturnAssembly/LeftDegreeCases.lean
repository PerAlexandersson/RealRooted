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

/-- Predicate-restricted sign-normalized positive-split x-subtraction cases
for the three Liu left-branch restored-degree cases. -/
def positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement P ∧
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P ∧
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement P

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

end LiuOppositeSigns
end RealRooted
