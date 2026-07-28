import RealRooted.LiuOppositeSigns.FactorReturnStatements
import RealRooted.LiuOppositeSigns.XSub.QuadraticCubic
import RealRooted.LiuOppositeSigns.XSub.CubicCubic

/-!
# Liu left factor-return translated right-family wrappers

This module contains the same-degree and successor-degree translated
right-family wrappers for the left factor-return branch.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- A right-successor sign-normalized x-subtraction leaf gives the translated
right-family target for the same-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    {P : ℕ → Prop}
    (hterminal :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hdelete_deg :
      (deleteRootFactor f r).natDegree + 1 = g.natDegree :=
    hleft.delete_natDegree_add_one_eq_of_sameDegree
      hsgn.left_ne_zero hdeg
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
        (-g).natDegree = (deleteRootFactor f r).natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg.symm
    have hGdeg : P (-g).natDegree := by
      simpa [Polynomial.natDegree_neg] using hgdeg
    have hsplit :=
      hterminal r hpair hqnn hGnn hdeg_pos hGdeg μ hμ
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
        g.natDegree = (-(deleteRootFactor f r)).natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg.symm
    have hsplit :=
      hterminal r hpair hQnn hgnn hdeg_pos hgdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

/-- A right-successor positive-split subtraction-family leaf gives the
translated right-family target for the same-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub
    (hsub :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyStatement := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    (P := fun _ => True)
    (positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hsub)
    hf hg hsgn hleft hdeg hcommon trivial

/-- A same-degree sign-normalized x-subtraction leaf gives the translated
right-family target for the successor-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    {P : ℕ → Prop}
    (hterminal :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree :=
    hleft.delete_natDegree_eq_of_succDegree hsgn.left_ne_zero hdeg
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
        (deleteRootFactor f r).natDegree = (-g).natDegree := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hGdeg : P (-g).natDegree := by
      simpa [Polynomial.natDegree_neg] using hgdeg
    have hsplit :=
      hterminal r hpair hqnn hGnn hdeg_pos hGdeg μ hμ
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
        (-(deleteRootFactor f r)).natDegree = g.natDegree := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hsplit :=
      hterminal r hpair hQnn hgnn hdeg_pos hgdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

/-- A same-degree positive-split subtraction-family leaf gives the translated
right-family target for the successor-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub
    (hsub : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyStatement := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    (P := fun _ => True)
    (positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hsub)
    hf hg hsgn hleft hdeg hcommon trivial

/-- Predicate-restricted right-successor sign-normalized x-subtraction leaves
give predicate-restricted translated right-family targets for the same-degree
Liu left branch. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hterminal :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicateStatement
      P := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    hterminal hf hg hsgn hleft hdeg hcommon hgdeg

/-- Predicate-restricted same-degree sign-normalized x-subtraction leaves give
predicate-restricted translated right-family targets for the successor-degree
Liu left branch. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hterminal :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P) :
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicateStatement
      P := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    hterminal hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-one right endpoint case for the translated same-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two right endpoint case for the translated same-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the translated same-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three right endpoint case for the translated same-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated same-degree Liu
right-family target. -/
theorem
    theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-zero right endpoint case for the translated successor-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-one right endpoint case for the translated successor-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Low-degree right endpoint cases for the translated successor-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two right endpoint reduction for the translated successor-degree
Liu right-family target, modulo the normalized monic quadratic/quadratic
x-subtraction leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two right endpoint case for the translated successor-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_two_of_monic
    xSubQuadraticQuadraticSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the translated
successor-degree Liu right-family target, modulo the normalized monic
quadratic/quadratic x-subtraction leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the translated successor-degree
Liu right-family target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_two_of_monic
    xSubQuadraticQuadraticSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three right endpoint reduction for the translated successor-degree
Liu right-family target, modulo the normalized monic cubic/cubic x-subtraction
leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three right endpoint reduction for the translated successor-degree
Liu right-family target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated
successor-degree Liu right-family target, modulo the normalized monic
cubic/cubic x-subtraction leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub_rightPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated successor-degree
Liu right-family target. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- The translated same-degree right-family leaf gives the translated
compatibility leaf by scaling an arbitrary nonnegative linear combination. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_rightFamily
    (hright :
      theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnSameDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnTranslatedCompatible_of_rightFamilyRelation
    (R := fun m n => m = n) hright

/-- The translated successor-degree right-family leaf gives the translated
compatibility leaf by scaling an arbitrary nonnegative linear combination. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_rightFamily
    (hright :
      theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnTranslatedCompatible_of_rightFamilyRelation
    (R := fun m n => m = n + 1) hright

/-- Predicate-restricted translated same-degree right-family targets give
predicate-restricted translated compatibility targets. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicate_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicateStatement
      P :=
  theorem21LeftFactorReturnTranslatedCompatible_of_rightPredicateRelation
    (R := fun m n => m = n) hright

/-- Predicate-restricted translated successor-degree right-family targets give
predicate-restricted translated compatibility targets. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicate_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicateStatement
      P :=
  theorem21LeftFactorReturnTranslatedCompatible_of_rightPredicateRelation
    (R := fun m n => m = n + 1) hright

/-- Predicate-restricted right-successor sign-normalized x-subtraction
families give predicate-restricted translated compatibility targets for the
same-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicateStatement
      P :=
  theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)

/-- Predicate-restricted same-degree sign-normalized x-subtraction families
give predicate-restricted translated compatibility targets for the
successor-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P) :
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicateStatement
      P :=
  theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)

/-- A right-successor positive-split subtraction-family leaf gives the
translated compatibility target for the same-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_xSub
    (hsub :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnSameDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_rightFamily
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub hsub)

/-- A same-degree positive-split subtraction-family leaf gives the translated
compatibility target for the successor-degree Liu left branch. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_xSub
    (hsub : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_rightFamily
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub hsub)

/-- Degree-one right endpoint case for the translated same-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_one
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-two right endpoint case for the translated same-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_two
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Endpoint cases through right degree two for the translated same-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_le_two
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-three right endpoint case for the translated same-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_right_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_three
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Endpoint cases through right degree three for the translated same-degree Liu
compatibility target. -/
theorem
    theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_right_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_right_natDegree_le_three
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-zero right endpoint case for the translated successor-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_zero
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-one right endpoint case for the translated successor-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_one
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Low-degree right endpoint cases for the translated successor-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 1) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_one
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-two right endpoint reduction for the translated successor-degree
Liu compatibility target, modulo the normalized monic quadratic/quadratic
x-subtraction leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_two_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-two right endpoint case for the translated successor-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_two_of_monic
    xSubQuadraticQuadraticSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the translated successor-degree
Liu compatibility target, modulo the normalized monic quadratic/quadratic
x-subtraction leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_le_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_two_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Endpoint cases through right degree two for the translated successor-degree
Liu compatibility target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_le_two_of_monic
    xSubQuadraticQuadraticSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three right endpoint reduction for the translated successor-degree
Liu compatibility target, modulo the normalized monic cubic/cubic x-subtraction
leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_three_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-three right endpoint reduction for the translated successor-degree
Liu compatibility target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated successor-degree
Liu compatibility target, modulo the normalized monic cubic/cubic x-subtraction
leaf. -/
theorem
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_right_natDegree_le_three_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Endpoint cases through right degree three for the translated successor-degree
Liu compatibility target. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Pointwise translated compatibility descent for the same-degree left
factor-return route. -/
theorem theorem21LeftFactorReturnSameDegree_of_pointwiseTranslatedCompatible
    {f g : ℝ[X]} {r s : ℝ}
    (hleft : LeftRootCountBranch f g r s)
    (htranslated :
      Compatible
        (X * (deleteRootFactor f r).comp (X + C r))
        (g.comp (X + C r))) :
    Compatible f g :=
  theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft htranslated

/-- The translated same-degree target gives the original same-degree
factor-return leaf by descending through the translation. -/
theorem theorem21LeftFactorReturnSameDegree_of_translatedCompatible
    (htranslated :
      theorem21LeftFactorReturnSameDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnSameDegreeStatement :=
  theorem21LeftFactorReturn_of_translatedCompatibleRelation
    (R := fun m n => m = n) htranslated

/-- Pointwise translated compatibility descent for the successor-degree left
factor-return route. -/
theorem theorem21LeftFactorReturnSuccDegree_of_pointwiseTranslatedCompatible
    {f g : ℝ[X]} {r s : ℝ}
    (hleft : LeftRootCountBranch f g r s)
    (htranslated :
      Compatible
        (X * (deleteRootFactor f r).comp (X + C r))
        (g.comp (X + C r))) :
    Compatible f g :=
  theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft htranslated

/-- The translated successor-degree target gives the original successor-degree
factor-return leaf by descending through the translation. -/
theorem theorem21LeftFactorReturnSuccDegree_of_translatedCompatible
    (htranslated :
      theorem21LeftFactorReturnSuccDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnSuccDegreeStatement :=
  theorem21LeftFactorReturn_of_translatedCompatibleRelation
    (R := fun m n => m = n + 1) htranslated

/-- Predicate-restricted translated same-degree compatibility targets give the
corresponding predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_translatedCompatiblePredicate
    {P : ℕ → Prop}
    (htranslated :
      theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicateStatement
        P) :
    theorem21LeftFactorReturnSameDegreePredicateStatement P :=
  theorem21LeftFactorReturnPredicate_of_translatedCompatibleRelation
    (R := fun m n => m = n) htranslated

/-- Predicate-restricted translated successor-degree compatibility targets
give the corresponding predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_translatedCompatiblePredicate
    {P : ℕ → Prop}
    (htranslated :
      theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicateStatement
        P) :
    theorem21LeftFactorReturnSuccDegreePredicateStatement P :=
  theorem21LeftFactorReturnPredicate_of_translatedCompatibleRelation
    (R := fun m n => m = n + 1) htranslated

/-- Predicate-restricted translated same-degree right-family targets give
predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnSameDegreePredicateStatement P :=
  theorem21LeftFactorReturnSameDegreePredicate_of_translatedCompatiblePredicate
    (theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hright)

/-- Predicate-restricted translated successor-degree right-family targets give
predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnSuccDegreePredicateStatement P :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_translatedCompatiblePredicate
    (theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hright)

/-- Predicate-restricted right-successor sign-normalized x-subtraction
families give predicate-restricted original same-degree factor-return targets. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnSameDegreePredicateStatement P :=
  theorem21LeftFactorReturnSameDegreePredicate_of_rightPredicate
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)

/-- Predicate-restricted same-degree sign-normalized x-subtraction families
give predicate-restricted original successor-degree factor-return targets. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P) :
    theorem21LeftFactorReturnSuccDegreePredicateStatement P :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_rightPredicate
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)

/-- A translated positive right-family leaf gives the original same-degree
factor-return leaf. -/
theorem theorem21LeftFactorReturnSameDegree_of_rightFamily
    (hright :
      theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnSameDegreeStatement :=
  theorem21LeftFactorReturnSameDegree_of_translatedCompatible
    (theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_rightFamily
      hright)

/-- A translated positive right-family leaf gives the original
successor-degree factor-return leaf. -/
theorem theorem21LeftFactorReturnSuccDegree_of_rightFamily
    (hright :
      theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnSuccDegreeStatement :=
  theorem21LeftFactorReturnSuccDegree_of_translatedCompatible
    (theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_rightFamily
      hright)

/-- Predicate-restricted translated right-family targets give pointwise
original same-degree factor-return targets. -/
theorem theorem21LeftFactorReturnSameDegree_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicateStatement
        P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    Compatible f g :=
  theorem21LeftFactorReturnSameDegreePredicate_of_rightPredicate hright
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Predicate-restricted translated right-family targets give pointwise
original successor-degree factor-return targets. -/
theorem theorem21LeftFactorReturnSuccDegree_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicateStatement
        P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_rightPredicate hright
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Predicate-restricted right-successor sign-normalized x-subtraction leaves
give pointwise original same-degree factor-return targets. -/
theorem theorem21LeftFactorReturnSameDegree_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    Compatible f g :=
  theorem21LeftFactorReturnSameDegree_of_rightPredicate
    (theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Predicate-restricted same-degree sign-normalized x-subtraction leaves give
pointwise original successor-degree factor-return targets. -/
theorem theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_rightPredicate
    (theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- A right-successor sign-normalized x-subtraction leaf gives the original
same-degree factor-return target. -/
theorem theorem21LeftFactorReturnSameDegree_of_xSub
    (hsub :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnSameDegreeStatement := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturnSameDegree_of_xSubPredicate
    (P := fun _ => True)
    (positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hsub)
    hf hg hsgn hleft hdeg hcommon trivial

/-- A same-degree sign-normalized x-subtraction leaf gives the original
successor-degree factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_xSub
    (hsub : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnSuccDegreeStatement := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    (P := fun _ => True)
    (positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hsub)
    hf hg hsgn hleft hdeg hcommon trivial

/-- Degree-one right endpoint case for the original same-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSameDegree_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible f g :=
  theorem21LeftFactorReturnSameDegree_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-one-right endpoint package for the original same-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_one :
    theorem21LeftFactorReturnSameDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one

/-- Degree-two right endpoint case for the original same-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSameDegree_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible f g :=
  theorem21LeftFactorReturnSameDegree_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two-right endpoint package for the original same-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_two :
    theorem21LeftFactorReturnSameDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two

/-- Endpoint cases through right degree two for the original same-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSameDegree_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible f g :=
  theorem21LeftFactorReturnSameDegree_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the original same-degree left
factor-return leaf, packaged as a predicate-restricted statement. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_two :
    theorem21LeftFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two

/-- Degree-three right endpoint case for the original same-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSameDegree_of_right_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible f g :=
  theorem21LeftFactorReturnSameDegree_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right endpoint package for the original same-degree left
factor-return leaf, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    theorem21LeftFactorReturnSameDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate
    (positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_three_of_monic
      hmono)

/-- Degree-three-right endpoint package for the original same-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_three :
    theorem21LeftFactorReturnSameDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_three_of_monic
    xSubQuadraticCubicSplits

/-- Endpoint cases through right degree three for the original same-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSameDegree_of_right_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible f g :=
  theorem21LeftFactorReturnSameDegree_of_xSubPredicate
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the original same-degree left
factor-return leaf, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    theorem21LeftFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate
    (positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Endpoint cases through right degree three for the original same-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_three :
    theorem21LeftFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_three_of_monic
    xSubQuadraticCubicSplits

/-- Degree-zero right endpoint case for the original successor-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-one right endpoint case for the original successor-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Low-degree right endpoint cases for the original successor-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 1) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-zero-right endpoint package for the original successor-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_zero :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n = 0) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero

/-- Degree-one-right endpoint package for the original successor-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_one :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one

/-- Low-degree right endpoint package for the original successor-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_one :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 1) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one

/-- Degree-two right endpoint reduction for the original successor-degree Liu
factor-return target, modulo the normalized monic quadratic/quadratic
x-subtraction leaf. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two right endpoint case for the original successor-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_right_natDegree_two_of_monic
    xSubQuadraticQuadraticSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two-right endpoint package for the original successor-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_two :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two

/-- Endpoint cases through right degree two for the original successor-degree
Liu factor-return target, modulo the normalized monic quadratic/quadratic
x-subtraction leaf. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_le_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the original successor-degree
Liu factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_right_natDegree_le_two_of_monic
    xSubQuadraticQuadraticSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the original successor-degree
left factor-return leaf, packaged as a predicate-restricted statement. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_two :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two

/-- Degree-three right endpoint reduction for the original successor-degree Liu
factor-return target, modulo the normalized monic cubic/cubic x-subtraction
leaf. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_xSubPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three right endpoint reduction for the original successor-degree Liu
factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right endpoint package for the original successor-degree left
factor-return leaf, modulo the normalized monic cubic/cubic x-subtraction
leaf. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
      hmono)

/-- Degree-three-right endpoint package for the original successor-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_three :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits

/-- Endpoint cases through right degree three for the original successor-degree
Liu factor-return target, modulo the normalized monic cubic/cubic x-subtraction
leaf. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible f g := by
  have hterminal :=
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono
  exact theorem21LeftFactorReturnSuccDegree_of_xSubPredicate hterminal
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the original successor-degree
Liu factor-return target. -/
theorem theorem21LeftFactorReturnSuccDegree_of_right_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible f g :=
  theorem21LeftFactorReturnSuccDegree_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the original successor-degree
left factor-return leaf, packaged as a predicate-restricted statement modulo the
normalized monic cubic/cubic x-subtraction leaf. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate
    (positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Endpoint cases through right degree three for the original successor-degree
left factor-return leaf, packaged as a predicate-restricted statement. -/
theorem theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_three :
    theorem21LeftFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits

end LiuOppositeSigns
end RealRooted
