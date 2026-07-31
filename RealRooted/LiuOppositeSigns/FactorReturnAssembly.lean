import RealRooted.LiuOppositeSigns.FactorReturnLeft
import RealRooted.LiuOppositeSigns.FactorReturnTwoDegree
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount

/-!
# Liu left factor-return case packages

This module contains the left-branch degree-case packages that assemble the
same-degree, successor-degree, and two-degree Liu factor-return branches.
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

/-- Right-branch factor-return target for an arbitrary endpoint degree
relation.  The relation is evaluated as `R g.natDegree f.natDegree`, matching
the right branch where `g` is the endpoint with the deleted root. -/
def theorem21RightFactorReturnRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        R g.natDegree f.natDegree →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            Compatible f g

/-- Predicate-restricted right-branch factor-return target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions on
`f.natDegree`, the endpoint used by the right branch. -/
def theorem21RightFactorReturnPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        R g.natDegree f.natDegree →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            P f.natDegree → Compatible f g

/-- Predicate-restricted right factor-return relation targets transport along
endpoint predicate implications. -/
theorem theorem21RightFactorReturnPredicateRelationStatement_of_imp
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnPredicateRelationStatement R Q) :
    theorem21RightFactorReturnPredicateRelationStatement R P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact hQ hf hg hsgn hright hdeg hcommon (hPQ _ hfdeg)

/-- The unrestricted right factor-return relation target is the `P := True`
case of the predicate-restricted relation target. -/
theorem theorem21RightFactorReturnPredicateRelation_true_of_relation
    {R : ℕ → ℕ → Prop}
    (hreturn : theorem21RightFactorReturnRelationStatement R) :
    theorem21RightFactorReturnPredicateRelationStatement R
      (fun _ => True) := by
  intro f g r s hf hg hsgn hright hdeg hcommon _
  exact hreturn hf hg hsgn hright hdeg hcommon

/-- A `P := True` right factor-return predicate relation target gives the
unrestricted relation target. -/
theorem theorem21RightFactorReturnRelation_of_predicate_true
    {R : ℕ → ℕ → Prop}
    (hreturn :
      theorem21RightFactorReturnPredicateRelationStatement R
        (fun _ => True)) :
    theorem21RightFactorReturnRelationStatement R := by
  intro f g r s hf hg hsgn hright hdeg hcommon
  exact hreturn hf hg hsgn hright hdeg hcommon trivial

/-- Same-degree right-branch factor-return target. -/
def theorem21RightFactorReturnSameDegreeStatement : Prop :=
  theorem21RightFactorReturnRelationStatement
    (fun m n => m = n)

/-- Succ-degree right-branch factor-return target. -/
def theorem21RightFactorReturnSuccDegreeStatement : Prop :=
  theorem21RightFactorReturnRelationStatement
    (fun m n => m = n + 1)

/-- Two-degree-gap right-branch factor-return target. -/
def theorem21RightFactorReturnTwoDegreeStatement : Prop :=
  theorem21RightFactorReturnRelationStatement
    (fun m n => m = n + 2)

/-- The three right-branch factor-return cases. -/
def theorem21RightFactorReturnDegreeCasesStatement : Prop :=
  theorem21RightFactorReturnSameDegreeStatement ∧
    theorem21RightFactorReturnSuccDegreeStatement ∧
      theorem21RightFactorReturnTwoDegreeStatement

/-- Predicate-restricted same-degree right-branch factor-return target.
The predicate records endpoint side conditions on `f.natDegree`, the endpoint
used by the right branch. -/
def theorem21RightFactorReturnSameDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnPredicateRelationStatement
    (fun m n => m = n) P

/-- Predicate-restricted successor-degree right-branch factor-return target.
The predicate records endpoint side conditions on `f.natDegree`, the endpoint
used by the right branch. -/
def theorem21RightFactorReturnSuccDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnPredicateRelationStatement
    (fun m n => m = n + 1) P

/-- A right all-combinations factor-return leaf for any degree relation gives
the corresponding compatibility factor-return leaf. -/
theorem theorem21RightFactorReturn_of_allComboRelation
    {R : ℕ → ℕ → Prop}
    (hright : theorem21RightFactorReturnAllComboRelationStatement R) :
    theorem21RightFactorReturnRelationStatement R := by
  intro f g r s hf hg hsgn hbranch hdeg hcommon
  exact Compatible.of_allComboRealRooted
    (hright hf hg hsgn hbranch hdeg hcommon)

/-- A same-degree all-combinations right leaf gives the corresponding
compatibility leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_allCombo
    (hright : theorem21RightFactorReturnSameDegreeAllComboStatement) :
    theorem21RightFactorReturnSameDegreeStatement :=
  theorem21RightFactorReturn_of_allComboRelation
    (R := fun m n => m = n) hright

/-- A successor-degree all-combinations right leaf gives the corresponding
compatibility leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_allCombo
    (hright : theorem21RightFactorReturnSuccDegreeAllComboStatement) :
    theorem21RightFactorReturnSuccDegreeStatement :=
  theorem21RightFactorReturn_of_allComboRelation
    (R := fun m n => m = n + 1) hright

/-- A two-degree-gap all-combinations right leaf gives the corresponding
compatibility leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_allCombo
    (hright : theorem21RightFactorReturnTwoDegreeAllComboStatement) :
    theorem21RightFactorReturnTwoDegreeStatement :=
  theorem21RightFactorReturn_of_allComboRelation
    (R := fun m n => m = n + 2) hright

/-- Right all-combinations factor-return degree cases give the corresponding
compatibility degree cases. -/
theorem theorem21RightFactorReturnDegreeCases_of_allComboCases
    (hcases : theorem21RightFactorReturnAllComboDegreeCasesStatement) :
    theorem21RightFactorReturnDegreeCasesStatement :=
  ⟨theorem21RightFactorReturnSameDegree_of_allCombo hcases.1,
    theorem21RightFactorReturnSuccDegree_of_allCombo hcases.2.1,
    theorem21RightFactorReturnTwoDegree_of_allCombo hcases.2.2⟩

/-- Predicate-restricted two-degree-gap right-branch factor-return target.
The predicate records endpoint side conditions on `f.natDegree`, the
lower-degree endpoint in the right branch. -/
def theorem21RightFactorReturnTwoDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnPredicateRelationStatement
    (fun m n => m = n + 2) P

/-- Predicate-restricted right two-degree factor-return targets transport along
endpoint predicate implications. -/
theorem theorem21RightFactorReturnTwoDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnTwoDegreePredicateStatement Q) :
    theorem21RightFactorReturnTwoDegreePredicateStatement P :=
  theorem21RightFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n + 2) hPQ hQ

/-- Predicate-restricted right same-degree factor-return targets transport
along endpoint predicate implications. -/
theorem theorem21RightFactorReturnSameDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnSameDegreePredicateStatement Q) :
    theorem21RightFactorReturnSameDegreePredicateStatement P :=
  theorem21RightFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n) hPQ hQ

/-- Predicate-restricted right successor-degree factor-return targets
transport along endpoint predicate implications. -/
theorem theorem21RightFactorReturnSuccDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnSuccDegreePredicateStatement Q) :
    theorem21RightFactorReturnSuccDegreePredicateStatement P :=
  theorem21RightFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n + 1) hPQ hQ

/-- General symmetry bridge from a left-branch factor-return theorem to the
matching right-branch theorem with the degree relation reversed. -/
theorem theorem21RightFactorReturn_of_leftDegreeRelation
    {R : ℕ → ℕ → Prop}
    (hleft :
      ∀ {p q : ℝ[X]} {a b : ℝ},
        p.Splits → q.Splits → OppositeLeadingSigns p q →
          LeftRootCountBranch p q a b →
            R p.natDegree q.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor p a) k ∧ Prec q k) →
                Compatible p q)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : R g.natDegree f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) :
    Compatible f g :=
  (hleft (p := g) (q := f) (a := s) (b := r)
    hg hf hsgn.symm hright.toLeftBranch_symm hdeg
    (rightDeletionPairCommonInterleaver_symm hcommon)).comm

/-- The right same-degree factor-return case follows from the left same-degree
case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSameDegree_of_leftSameDegree
    (hleft : theorem21LeftFactorReturnSameDegreeStatement) :
    theorem21RightFactorReturnSameDegreeStatement := by
  intro f g r s hf hg hsgn hright hdeg hcommon
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n) hleft hf hg hsgn hright hdeg hcommon

/-- Predicate-restricted same-degree left factor-return targets give the
corresponding right-branch predicate targets by symmetry. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnSameDegreePredicateStatement P) :
    theorem21RightFactorReturnSameDegreePredicateStatement P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n ∧ P n)
    (fun hp hq hsgn' hleft' hrel hcommon' =>
      hleft hp hq hsgn' hleft' hrel.1 hcommon' hrel.2)
    hf hg hsgn hright ⟨hdeg, hfdeg⟩ hcommon

/-- Degree-one-left endpoint package for the right same-degree factor-return
target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_one :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n = 1)
    theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_one

/-- Degree-two-left endpoint package for the right same-degree factor-return
target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_two :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_two

/-- Endpoint cases through left degree two for the right same-degree
factor-return target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_two :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 2)
    theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_two

/-- Degree-three-left endpoint package for the right same-degree factor-return
target, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n = 3)
    (theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_three_of_monic
      hmono)

/-- Degree-three-left endpoint package for the right same-degree factor-return
target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three_of_monic
    xSubQuadraticCubicSplits

/-- Endpoint cases through left degree three for the right same-degree
factor-return target, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 3)
    (theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Endpoint cases through left degree three for the right same-degree
factor-return target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three_of_monic
    xSubQuadraticCubicSplits

/-- Degree-one-left endpoint case for the right same-degree factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 1) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right same-degree factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree two for the right same-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 2) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-three-left endpoint case for the right same-degree factor-return leaf,
modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three_of_monic
    hmono hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-three-left endpoint case for the right same-degree factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegree_of_left_natDegree_three_of_monic
    xSubQuadraticCubicSplits hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree three for the right same-degree
factor-return leaf, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three_of_monic
    hmono hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree three for the right same-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegree_of_left_natDegree_le_three_of_monic
    xSubQuadraticCubicSplits hf hg hsgn hright hdeg hcommon hfdeg

/-- The right successor-degree factor-return case follows from the left
successor-degree case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSuccDegree_of_leftSuccDegree
    (hleft : theorem21LeftFactorReturnSuccDegreeStatement) :
    theorem21RightFactorReturnSuccDegreeStatement := by
  intro f g r s hf hg hsgn hright hdeg hcommon
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n + 1) hleft hf hg hsgn hright hdeg hcommon

/-- Predicate-restricted successor-degree left factor-return targets give the
corresponding right-branch predicate targets by symmetry. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnSuccDegreePredicateStatement P) :
    theorem21RightFactorReturnSuccDegreePredicateStatement P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n + 1 ∧ P n)
    (fun hp hq hsgn' hleft' hrel hcommon' =>
      hleft hp hq hsgn' hleft' hrel.1 hcommon' hrel.2)
    hf hg hsgn hright ⟨hdeg, hfdeg⟩ hcommon

/-- Degree-zero-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_zero :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 0) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 0)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_zero

/-- Degree-one-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_one :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 1)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_one

/-- Low-degree left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_one :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 1) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 1)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_one

/-- Degree-two-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_two :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_two

/-- Endpoint cases through left degree two for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_two :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 2)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_two

/-- Degree-three-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_three :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 3)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_three

/-- Endpoint cases through left degree three for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_three :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 3)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_three

/-- Degree-zero-left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 0) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_zero
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-one-left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 1) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Low-degree left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 1) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree two for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 2) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-three-left endpoint case for the right successor-degree factor-return
leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 3) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_three
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree three for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 3) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_three
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Predicate-parameterized symmetry bridge for right two-degree factor-return
cases.  The predicate records endpoint restrictions such as degree `0`, degree
`1`, or degree `≤ 1` on the swapped right endpoint. -/
theorem theorem21RightFactorReturnTwoDegree_of_leftPredicate
    {P : ℕ → Prop}
    (hleft :
      ∀ {p q : ℝ[X]} {a b : ℝ},
        p.Splits → q.Splits → OppositeLeadingSigns p q →
          LeftRootCountBranch p q a b →
            p.natDegree = q.natDegree + 2 →
              (∃ k : ℝ[X], Prec (deleteRootFactor p a) k ∧ Prec q k) →
                P q.natDegree → Compatible p q)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : P f.natDegree) :
    Compatible f g :=
  theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n + 2 ∧ P n)
    (fun hp hq hsgn' hleft' hrel hcommon' =>
      hleft hp hq hsgn' hleft' hrel.1 hcommon' hrel.2)
    hf hg hsgn hright ⟨hdeg, hfdeg⟩ hcommon

/-- Predicate-restricted left two-degree factor-return targets give the
corresponding right-branch predicate targets by symmetry. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnTwoDegreePredicateStatement P) :
    theorem21RightFactorReturnTwoDegreePredicateStatement P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact theorem21RightFactorReturnTwoDegree_of_leftPredicate
    hleft hf hg hsgn hright hdeg hcommon hfdeg

/-- A `P := True` right-branch factor-return predicate target gives the
unrestricted right two-degree factor-return target. -/
theorem theorem21RightFactorReturnTwoDegree_of_predicate_true
    (hright :
      theorem21RightFactorReturnTwoDegreePredicateStatement
        (fun _ => True)) :
    theorem21RightFactorReturnTwoDegreeStatement :=
  theorem21RightFactorReturnRelation_of_predicate_true
    (R := fun m n => m = n + 2) hright

/-- The unrestricted right two-degree factor-return target is the `P := True`
case of the predicate-restricted target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_true_of_twoDegree
    (hright : theorem21RightFactorReturnTwoDegreeStatement) :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun _ => True) :=
  theorem21RightFactorReturnPredicateRelation_true_of_relation
    (R := fun m n => m = n + 2) hright

/-- The right two-degree-gap factor-return case follows from the left
two-degree-gap case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnTwoDegree_of_leftTwoDegree
    (hleft : theorem21LeftFactorReturnTwoDegreeStatement) :
    theorem21RightFactorReturnTwoDegreeStatement :=
  theorem21RightFactorReturnTwoDegree_of_predicate_true
    (theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
      (P := fun _ => True)
      (theorem21LeftFactorReturnTwoDegreePredicate_true_of_twoDegree hleft))

/-- Left factor-return degree cases give the matching right cases by symmetry. -/
theorem theorem21RightFactorReturnDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21RightFactorReturnDegreeCasesStatement :=
  ⟨theorem21RightFactorReturnSameDegree_of_leftSameDegree hcases.1,
    theorem21RightFactorReturnSuccDegree_of_leftSuccDegree hcases.2.1,
    theorem21RightFactorReturnTwoDegree_of_leftTwoDegree hcases.2.2⟩

/-- Low-degree left-endpoint cases for the right two-degree factor-return
target, packaged as a predicate-restricted statement. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_one :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 1) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 1)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_one

/-- Constant-left-endpoint package for the right two-degree factor-return
target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_zero :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 0) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 0)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_zero

/-- Degree-one-left-endpoint package for the right two-degree factor-return
target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_one :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 1)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_one

/-- Endpoint cases through left degree two for the right two-degree
factor-return target, packaged as a predicate-restricted statement. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_two :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 2)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_two

/-- Degree-two-left endpoint package for the right two-degree factor-return
target, modulo the normalized monic arithmetic leaf. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement) :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    (theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_two_of_monic
      hmono)

/-- Degree-two-left endpoint package for the right two-degree factor-return
target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_two

/-- Constant-left-endpoint base case for the right two-degree factor-return
leaf, obtained by symmetry from the left constant-right base case. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 0) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_zero
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-one-left-endpoint base case for the right two-degree factor-return
leaf, obtained by symmetry from the left degree-one-right base case. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 1) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Low-degree left-endpoint cases for the right two-degree factor-return
leaf, obtained by symmetry from the left low-degree-right wrapper. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 1) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree two for the right two-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 2) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right two-degree factor-return
leaf, modulo the normalized monic arithmetic leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two_of_monic
    hmono hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right two-degree factor-return
leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two
    hf hg hsgn hright hdeg hcommon hfdeg

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
      P := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon hgdeg
    exact (hQ hf hg hsgn).1 hleft hcommon (hPQ _ hgdeg)
  · intro hright hcommon hfdeg
    exact (hQ hf hg hsgn).2 hright hcommon (hPQ _ hfdeg)

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

/-- Degree-case split needed to prove the factor-return principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreeStatement ∧
        theorem21RightFactorReturnSameDegreeStatement ∧
          theorem21RightFactorReturnSuccDegreeStatement ∧
            theorem21RightFactorReturnTwoDegreeStatement

/-- Left and right factor-return degree cases assemble into the full six-case
package. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    (hleft : theorem21LeftFactorReturnDegreeCasesStatement)
    (hright : theorem21RightFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

/-- Left projection from a six-case ordinary factor-return package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_factorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case ordinary factor-return package. -/
theorem theorem21RightFactorReturnDegreeCases_of_factorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21RightFactorReturnDegreeCasesStatement :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

/-- All-combinations factor-return degree cases give the corresponding
compatibility factor-return degree cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    (theorem21LeftFactorReturnDegreeCases_of_allComboCases
      (theorem21LeftFactorReturnAllComboDegreeCases_of_allComboFactorCases
        hcases))
    (theorem21RightFactorReturnDegreeCases_of_allComboCases
      (theorem21RightFactorReturnAllComboDegreeCases_of_allComboFactorCases
        hcases))

/-- Left factor-return degree cases supply all six left/right cases by
symmetry. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnDegreeCases_of_leftCases hcases)

/-- The explicit factor-return principle follows from its six restored-degree
cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  let hleftCases := theorem21LeftFactorReturnDegreeCases_of_factorCases hcases
  let hrightCases := theorem21RightFactorReturnDegreeCases_of_factorCases hcases
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

/-- It is enough to prove the left-branch factor-return cases; the right branch
is symmetric. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
      hcases)

/-- All-combinations factor-return degree cases imply the compatibility
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases imply the compatibility
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_allComboCases hcases)

/-- Translated compatibility degree cases imply the factor-return principle
used by the reverse direction. -/
theorem
    theorem21DeletionPairCommonInterleaverFactorReturn_of_translatedCompatibleCases
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_translatedCompatibleCases hcases)

/-- Translated right-family degree cases imply the factor-return principle
used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_translatedRightFamilyCases
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_translatedRightFamilyCases
      hcases)

/-- A bundled sign-normalized positive-split x-subtraction case package
implies the factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_xSubCasePackage
      hcases)

/-- Sign-normalized positive-split x-subtraction cases imply the
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- Since the same-degree and left-successor x-subtraction cases are proved, the
reverse factor-return principle only needs the remaining right-successor
x-subtraction leaf. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_rightSucc_xSub
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCases
    hrightSucc positiveSplitSameDegreeTranslatedXSubRightFamily
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and a bundled sign-normalized
positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_factorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and a bundled
sign-normalized positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and a bundled
sign-normalized positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCasePackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_factorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
a bundled sign-normalized positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and sign-normalized positive-split
x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and sign-normalized
positive-split x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- The factor-return principle follows from same/succ left leaves and the
translated two-degree compatibility target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_translatedTwo
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo
      hsame hsucc htwo)

/-- The factor-return principle follows from same/succ left leaves and the
translated right-family two-degree target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_rightFamily
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_rightFamily
      hsame hsucc hright)

/-- The factor-return principle follows from same/succ left leaves and the
sign-normalized positive-split subtraction-family leaf. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_xSub
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_rightFamily
    hsame hsucc
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub hsub)

end LiuOppositeSigns
end RealRooted
