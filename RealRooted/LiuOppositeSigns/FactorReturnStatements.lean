import RealRooted.LiuOppositeSigns.DeletionBranches

/-!
# Liu factor-return statement interface

This module contains the statement-level factor-return packages, target
aliases, and left/right symmetry adapters used in the reverse direction of Liu
Theorem 2.1.
The proof-heavy degree branches and final theorem assembly remain in
`RealRooted.LiuOppositeSigns.Theorem`.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Swap the common-right-interleaver witness in a right deletion pair. -/
theorem rightDeletionPairCommonInterleaver_symm {f g : ℝ[X]} {s : ℝ}
    (hcommon : ∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl (deleteRootFactor g s) k) :
    ∃ k : ℝ[X], StrictInterl (deleteRootFactor g s) k ∧ StrictInterl f k := by
  rcases hcommon with ⟨k, hfk, hgk⟩
  exact ⟨k, hgk, hfk⟩

/-- Predicate-restricted left-branch factor-return target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions on
`g.natDegree`. -/
def theorem21LeftFactorReturnPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
            P g.natDegree → Compatible f g

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

/-- Predicate-restricted two-degree-gap left-branch factor-return target.
The predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnTwoDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnPredicateRelationStatement
    (fun m n => m = n + 2) P

/-- Predicate-restricted translated compatibility target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions on
`g.natDegree`. -/
def theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
            P g.natDegree →
              Compatible
                (X * (deleteRootFactor f r).comp (X + C r))
                (g.comp (X + C r))

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

/-- Predicate-restricted translated compatibility targets give the
corresponding predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnPredicate_of_translatedCompatibleRelation
    {R : ℕ → ℕ → Prop} {P : ℕ → Prop}
    (htranslated :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
                P g.natDegree →
                  Compatible
                    (X * (deleteRootFactor f r).comp (X + C r))
                    (g.comp (X + C r))) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
              P g.natDegree → Compatible f g := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft
    (htranslated hf hg hsgn hleft hdeg hcommon hgdeg)

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

/-- Predicate-restricted translated two-degree compatibility target.  The
predicate records endpoint side conditions on `g.natDegree`. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedCompatiblePredicateRelationStatement
    (fun m n => m = n + 2) P

/-- Predicate-restricted translated right-family target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions such
as fixed right degree or a low-degree bound. -/
def theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        R f.natDegree g.natDegree →
          (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
            P g.natDegree →
              ∀ μ : ℝ, 0 < μ →
                (X * (deleteRootFactor f r).comp (X + C r) +
                    C μ * g.comp (X + C r)).Splits

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
              (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
                P g.natDegree →
                  ∀ μ : ℝ, 0 < μ →
                    (X * (deleteRootFactor f r).comp (X + C r) +
                        C μ * g.comp (X + C r)).Splits) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k) →
              P g.natDegree →
                Compatible
                  (X * (deleteRootFactor f r).comp (X + C r))
                  (g.comp (X + C r)) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft (hright hf hg hsgn hleft hdeg hcommon hgdeg)

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

/-- Predicate-restricted form of the translated two-degree right-family
target.  The predicate records endpoint side conditions such as `natDegree = 0`,
`natDegree = 1`, or `natDegree ≤ 1`. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelationStatement
    (fun m n => m = n + 2) P

end LiuOppositeSigns
end RealRooted
