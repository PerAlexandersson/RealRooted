import RealRooted.LiuOppositeSigns.FactorReturnAssembly.LeftDegreeCases

/-!
# Liu right factor-return degree cases

This module obtains the right deletion-branch degree cases from the left cases
by symmetry and packages their endpoint-degree specializations.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Predicate-restricted right-branch factor-return target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions on
`f.natDegree`, the endpoint used by the right branch. -/
def theorem21RightFactorReturnPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        R g.natDegree f.natDegree →
          (∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl (deleteRootFactor g s) k) →
            P f.natDegree → Compatible f g

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

/-- Predicate-restricted two-degree-gap right-branch factor-return target.
The predicate records endpoint side conditions on `f.natDegree`, the
lower-degree endpoint in the right branch. -/
def theorem21RightFactorReturnTwoDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnPredicateRelationStatement
    (fun m n => m = n + 2) P

/-- General symmetry bridge from a left-branch factor-return theorem to the
matching right-branch theorem with the degree relation reversed. -/
theorem theorem21RightFactorReturn_of_leftDegreeRelation
    {R : ℕ → ℕ → Prop}
    (hleft :
      ∀ {p q : ℝ[X]} {a b : ℝ},
        p.Splits → q.Splits → OppositeLeadingSigns p q →
          LeftRootCountBranch p q a b →
            R p.natDegree q.natDegree →
              (∃ k : ℝ[X], StrictInterl (deleteRootFactor p a) k ∧ StrictInterl q k) →
                Compatible p q)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : R g.natDegree f.natDegree)
    (hcommon : ∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl (deleteRootFactor g s) k) :
    Compatible f g :=
  (hleft (p := g) (q := f) (a := s) (b := r)
    hg hf hsgn.symm hright.toLeftBranch_symm hdeg
    (rightDeletionPairCommonInterleaver_symm hcommon)).comm

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
              (∃ k : ℝ[X], StrictInterl (deleteRootFactor p a) k ∧ StrictInterl q k) →
                P q.natDegree → Compatible p q)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl (deleteRootFactor g s) k)
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

end LiuOppositeSigns
end RealRooted
