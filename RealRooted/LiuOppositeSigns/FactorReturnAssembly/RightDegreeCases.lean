import RealRooted.LiuOppositeSigns.FactorReturnAssembly.LeftDegreeCases

/-!
# Liu right factor-return degree cases

This module obtains the right deletion-branch degree cases from the left cases
by symmetry and packages their endpoint-degree specializations.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

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

end LiuOppositeSigns
end RealRooted
