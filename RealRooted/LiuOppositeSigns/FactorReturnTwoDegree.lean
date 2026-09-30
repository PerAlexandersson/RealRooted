import RealRooted.LiuOppositeSigns.FactorReturnStatements
import RealRooted.LiuOppositeSigns.XSub.LeftSucc
import RealRooted.LiuOppositeSigns.XSub.SplittingTools
import RealRooted.MaWang

/-!
# Liu two-degree factor-return translated right-family bridge

This module contains the translated right-family bridge, translated-compatible
wrappers, and original factor-return wrappers for the two-degree left
factor-return branch.  Degree-case packaging and symmetry live downstream.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- A degree-specific sign-normalized x-subtraction leaf gives the translated
right-family target after the Liu sign normalization.  The predicate records
endpoint restrictions such as a fixed degree or a low-degree bound. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub_rightPredicate
    {P : ℕ → Prop}
    (hterminal :
      ∀ {p q : ℝ[X]} {a : ℝ},
        PositiveSplitRootCountPair p q →
        HasNonnegCoeffs (p.comp (X + C a)) →
        HasNonnegCoeffs (q.comp (X + C a)) →
        p.natDegree = q.natDegree + 1 →
        P q.natDegree →
        ∀ μ : ℝ, 0 < μ →
          (X * p.comp (X + C a) - C μ * q.comp (X + C a)).Splits)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (_hcommon : ∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k)
    (hgdeg : P g.natDegree) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    hleft.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  have hroots :=
    hleft.deletionPair_roots_le_left_largest hsgn.left_ne_zero
  rcases hleft.positiveSplitDeletionCount hsgn hf hg with hpair | hpair
  · have hqnn :
        HasNonnegCoeffs ((deleteRootFactor f r).comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpair.left_pos hpair.left_splits hroots.1
    have hGnn : HasNonnegCoeffs ((-g).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpair.right_pos hpair.right_splits ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
    have hdeg_pos :
        (deleteRootFactor f r).natDegree = (-g).natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hGdeg : P (-g).natDegree := by simpa [Polynomial.natDegree_neg] using hgdeg
    have hsplit :=
      hterminal hpair hqnn hGnn hdeg_pos hGdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg] using hsplit
  · have hQnn :
        HasNonnegCoeffs ((-(deleteRootFactor f r)).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpair.left_pos hpair.left_splits ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    have hgnn : HasNonnegCoeffs (g.comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpair.right_pos hpair.right_splits hroots.2
    have hdeg_pos :
        (-(deleteRootFactor f r)).natDegree = g.natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hsplit :=
      hterminal hpair hQnn hgnn hdeg_pos hgdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

/-- Predicate-restricted positive-split x-subtraction families give the
corresponding translated two-degree right-family predicate target after the
Liu sign normalization. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hterminal :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      P := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub_rightPredicate
    (fun {p} {q} {a} hpair hpnn hqnn hpqdeg hp μ hμ =>
      hterminal a hpair hpnn hqnn hpqdeg hp μ hμ)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Predicate-restricted translated right-family targets give the corresponding
pointwise translated compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], StrictInterl (deleteRootFactor f r) k ∧ StrictInterl g k)
    (hgdeg : P g.natDegree) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_rightPredicateRelation
    (R := fun m n => m = n + 2) hright
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Predicate-restricted translated right-family targets give
predicate-restricted translated compatibility targets. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      P := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightPredicate
    hright hf hg hsgn hleft hdeg hcommon hgdeg

/-- Predicate-restricted translated compatibility targets give the
corresponding predicate-restricted original two-degree factor-return targets. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_translatedCompatiblePredicate
    {P : ℕ → Prop}
    (htranslated :
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
        P) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement P :=
  theorem21LeftFactorReturnPredicate_of_translatedCompatibleRelation
    (R := fun m n => m = n + 2) htranslated

/-- Predicate-restricted translated right-family targets give
predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement P :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_translatedCompatiblePredicate
    (theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hright)

/-- Predicate-restricted positive-split x-subtraction families give
predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement P :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_rightPredicate
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)

end LiuOppositeSigns
end RealRooted
