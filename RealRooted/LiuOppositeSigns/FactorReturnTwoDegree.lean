import RealRooted.LiuOppositeSigns.FactorReturnStatements
import RealRooted.LiuOppositeSigns.XSub.LeftSuccDegreeThree

/-!
# Liu two-degree factor-return translated right-family bridge

This module contains the translated right-family bridge, translated-compatible
wrappers, and original factor-return wrappers for the two-degree left
factor-return branch.  Degree-case packaging and symmetry live downstream.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- A left endpoint cannot be in `Prec` with a right endpoint of one lower
degree.  This guards against a tempting but degree-impossible #64 route. -/
theorem not_prec_of_natDegree_eq_succ_left {f g : ℝ[X]}
    (hdeg : f.natDegree = g.natDegree + 1) :
    ¬ Prec f g :=
  not_prec_of_right_natDegree_lt_left (by lia)

/-- In the two-degree Liu left branch, orienting the translated deletion pair
as `deleteRootFactor f r ≺ g` is degree-impossible. -/
theorem LeftRootCountBranch.not_translatedDeletionPrec_of_twoDegree
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hdeg : f.natDegree = g.natDegree + 2) :
    ¬ (Prec ((deleteRootFactor f r).comp (X + C r)) ((-g).comp (X + C r)) ∨
        Prec ((-(deleteRootFactor f r)).comp (X + C r)) (g.comp (X + C r))) := by
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    h.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  intro horient
  rcases horient with hprec | hprec
  · have hdeg' :
        ((deleteRootFactor f r).comp (X + C r)).natDegree =
          ((-g).comp (X + C r)).natDegree + 1 := by
      simpa [Polynomial.natDegree_comp, Polynomial.natDegree_neg] using hdelete_deg
    exact (not_prec_of_natDegree_eq_succ_left hdeg') hprec
  · have hdeg' :
        ((-(deleteRootFactor f r)).comp (X + C r)).natDegree =
          (g.comp (X + C r)).natDegree + 1 := by
      simpa [Polynomial.natDegree_comp, Polynomial.natDegree_neg] using hdelete_deg
    exact (not_prec_of_natDegree_eq_succ_left hdeg') hprec

/-- The stronger boundary-`Prec` route is also degree-impossible in the
two-degree Liu left branch: the restored endpoint has degree two more than
`g`. -/
theorem LeftRootCountBranch.not_translatedBoundaryPrec_of_twoDegree
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hdeg : f.natDegree = g.natDegree + 2) :
    ¬ Prec (g.comp (X + C r))
        (X * (deleteRootFactor f r).comp (X + C r)) := by
  have hdelete_ne : deleteRootFactor f r ≠ 0 :=
    h.delete_ne_zero hsgn.left_ne_zero
  have hdelete_shift_ne :
      (deleteRootFactor f r).comp (X + C r) ≠ 0 :=
    (Polynomial.comp_X_add_C_ne_zero_iff).2 hdelete_ne
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    h.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  have hshift_deg :
      ((deleteRootFactor f r).comp (X + C r)).natDegree =
        (g.comp (X + C r)).natDegree + 1 := by
    simpa [Polynomial.natDegree_comp] using hdelete_deg
  have hrestored_deg :
      (X * (deleteRootFactor f r).comp (X + C r)).natDegree =
        (g.comp (X + C r)).natDegree + 2 := by
    rw [natDegree_mul X_ne_zero hdelete_shift_ne, natDegree_X, hshift_deg]
    lia
  have hgap :
      (g.comp (X + C r)).natDegree + 1 <
        (X * (deleteRootFactor f r).comp (X + C r)).natDegree := by
    rw [hrestored_deg]
    lia
  exact not_prec_of_left_natDegree_succ_lt_right hgap

/-- A `P := True` translated right-family predicate target gives the
unrestricted translated right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_predicate_true
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        (fun _ => True)) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement :=
  theorem21LeftFactorReturnTranslatedRightFamilyRelation_of_predicate_true
    (R := fun m n => m = n + 2) hright

/-- The unrestricted translated right-family target is the `P := True` case of
the predicate-restricted target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_true_of_rightFamily
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun _ => True) :=
  theorem21LeftFactorReturnTranslatedRightFamilyPredicateRelation_true_of_relation
    (R := fun m n => m = n + 2) hright

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
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
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

/-- Pack the constant-right endpoint terminal as a predicate-restricted
translated right-family target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_zero :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n = 0) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero

/-- Pack the degree-one-right endpoint terminal as a predicate-restricted
translated right-family target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_one :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n = 1) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one

/-- Pack the low-degree-right endpoint terminals as a predicate-restricted
translated right-family target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_le_one :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n ≤ 1) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one

/-- Pack the degree-two-right endpoint terminal as a predicate-restricted
translated right-family target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_two :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n = 2) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two

/-- Pack the endpoint cases through right degree two as a predicate-restricted
translated right-family target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_le_two :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n ≤ 2) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two

/-- Pack the degree-three-right endpoint terminal as a predicate-restricted
translated right-family target, modulo the normalized monic quartic/cubic
arithmetic leaf. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
      hmono)

/-- Pack the degree-three-right endpoint terminal as a predicate-restricted
translated right-family target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_three :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three

/-- Pack the endpoint cases through right degree three as a predicate-restricted
translated right-family target, modulo the normalized monic quartic/cubic
arithmetic leaf. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    (positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Pack the endpoint cases through right degree three as a predicate-restricted
translated right-family target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_le_three :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three

/-- A fixed right-degree sign-normalized x-subtraction leaf gives the translated
right-family target after the Liu sign normalization. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub_rightDegree
    {n : ℕ}
    (hterminal :
      ∀ {p q : ℝ[X]} {a : ℝ},
        PositiveSplitRootCountPair p q →
        HasNonnegCoeffs (p.comp (X + C a)) →
        HasNonnegCoeffs (q.comp (X + C a)) →
        p.natDegree = q.natDegree + 1 →
        q.natDegree = n →
        ∀ μ : ℝ, 0 < μ →
          (X * p.comp (X + C a) - C μ * q.comp (X + C a)).Splits)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = n) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
    (P := fun m => m = n)
    (fun {p} {q} a hpair hpnn hqnn hpqdeg hqdeg μ hμ =>
      hterminal (p := p) (q := q) (a := a)
        hpair hpnn hqnn hpqdeg hqdeg μ hμ)
    hf hg hsgn hleft hdeg _hcommon hgdeg

/-- The sign-normalized positive-split subtraction-family leaf gives the
translated one-parameter target for the two-degree Liu left branch. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement :=
  theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_predicate_true
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_true_of_xSub
        hsub))

/-- Constant-right-endpoint base case for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_zero
    hf hg hsgn hleft hdeg _hcommon hgdeg

/-- Degree-one-right-endpoint case for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_one
    hf hg hsgn hleft hdeg _hcommon hgdeg

/-- Low-degree right-endpoint cases for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_le_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two-right-endpoint case for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_le_two
      hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right-endpoint case for the translated two-degree Liu
right-family target, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_rightDeg_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_three_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right-endpoint case for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_rightDeg_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_three
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated two-degree Liu
right-family target, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_rightDeg_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_le_three_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_rightDeg_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_le_three
      hf hg hsgn hleft hdeg hcommon hgdeg

/-- Pointwise right-family form of the translated two-degree Liu compatibility
target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_pointwiseRightFamily
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hright : ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) :=
  theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft hright

/-- The positive right-pencil translated leaf gives the translated
compatibility leaf by scaling an arbitrary nonnegative linear combination. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightFamily
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnTranslatedCompatible_of_rightFamilyRelation
    (R := fun m n => m = n + 2) hright

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
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
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

/-- Predicate-restricted positive-split x-subtraction families give
predicate-restricted translated compatibility targets. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      P :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)

/-- Pack the constant-right endpoint terminal as a predicate-restricted
translated compatibility target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_zero :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n = 0) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n = 0)
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_zero

/-- Pack the degree-one-right endpoint terminal as a predicate-restricted
translated compatibility target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_one :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n = 1) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n = 1)
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_one

/-- Pack the low-degree-right endpoint terminals as a predicate-restricted
translated compatibility target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_le_one :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n ≤ 1) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n ≤ 1)
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_le_one

/-- Pack the degree-two-right endpoint terminal as a predicate-restricted
translated compatibility target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_two :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n = 2) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n = 2)
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_two

/-- Pack the endpoint cases through right degree two as a predicate-restricted
translated compatibility target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_le_two :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n ≤ 2)
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_right_natDegree_le_two

/-- Pack the degree-three-right endpoint terminal as a predicate-restricted
translated compatibility target, modulo the normalized monic quartic/cubic
arithmetic leaf. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n = 3)
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_three_of_monic
      hmono)

/-- Pack the degree-three-right endpoint terminal as a predicate-restricted
translated compatibility target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_three :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n = 3)
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_three

/-- Pack the endpoint cases through right degree three as a
predicate-restricted translated compatibility target, modulo the normalized
monic quartic/cubic arithmetic leaf. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n ≤ 3)
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_le_three_of_monic
      hmono)

/-- Pack the endpoint cases through right degree three as a
predicate-restricted translated compatibility target. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_le_three :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
    (P := fun n => n ≤ 3)
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_rightDeg_le_three

/-- A `P := True` translated compatibility predicate target gives the
unrestricted translated compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_predicate_true
    (htranslated :
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
        (fun _ => True)) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnTranslatedCompatibleRelation_of_predicate_true
    (R := fun m n => m = n + 2) htranslated

/-- The unrestricted translated compatibility target is the `P := True` case
of the predicate-restricted target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_true_of_compatible
    (htranslated :
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
      (fun _ => True) :=
  theorem21LeftFactorReturnTranslatedCompatiblePredicateRelation_true_of_relation
    (R := fun m n => m = n + 2) htranslated

/-- Constant-right-endpoint base case for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_zero
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-one-right-endpoint case for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Low-degree right-endpoint cases for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 1) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_le_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two-right-endpoint case for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_right_natDegree_le_two
      hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right-endpoint case for the translated two-degree Liu
compatibility target, modulo the normalized monic quartic/cubic arithmetic
leaf. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightDeg_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_three_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right-endpoint case for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightDeg_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_three
      hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated two-degree Liu
compatibility target, modulo the normalized monic quartic/cubic arithmetic
leaf. -/
theorem
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightDeg_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_le_three_of_monic
      hmono hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightDeg_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  exact
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightDeg_le_three
      hf hg hsgn hleft hdeg hcommon hgdeg

/-- The sign-normalized positive-split subtraction-family leaf gives the
translated compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_xSub
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_predicate_true
    (theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_xSubPredicate
      (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_true_of_xSub
        hsub))

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

/-- Pointwise translated compatibility descent for the two-degree left
factor-return route. -/
theorem theorem21LeftFactorReturnTwoDegree_of_pointwiseTranslatedCompatible
    {f g : ℝ[X]} {r s : ℝ}
    (hleft : LeftRootCountBranch f g r s)
    (htranslated :
      Compatible
        (X * (deleteRootFactor f r).comp (X + C r))
        (g.comp (X + C r))) :
    Compatible f g :=
  theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft htranslated

/-- The translated compatibility target gives the original two-degree
factor-return leaf by descending through the translation. -/
theorem theorem21LeftFactorReturnTwoDegree_of_translatedCompatible
    (htranslated :
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnTwoDegreeStatement :=
  theorem21LeftFactorReturn_of_translatedCompatibleRelation
    (R := fun m n => m = n + 2) htranslated

/-- A translated positive right-family leaf gives the original two-degree
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_rightFamily
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeStatement :=
  theorem21LeftFactorReturnTwoDegree_of_translatedCompatible
    (theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightFamily
      hright)

/-- Predicate-restricted translated right-family targets give the corresponding
original two-degree factor-return target. -/
theorem theorem21LeftFactorReturnTwoDegree_of_rightPredicate
    {P : ℕ → Prop}
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_pointwiseTranslatedCompatible hleft
    (theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightPredicate
      hright hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Predicate-restricted left-successor sign-normalized x-subtraction leaves
give pointwise original two-degree factor-return targets. -/
theorem theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    {P : ℕ → Prop}
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : P g.natDegree) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_rightPredicate
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsub)
    hf hg hsgn hleft hdeg hcommon hgdeg

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

/-- A `P := True` original factor-return predicate target gives the
unrestricted two-degree factor-return target. -/
theorem theorem21LeftFactorReturnTwoDegree_of_predicate_true
    (htwo :
      theorem21LeftFactorReturnTwoDegreePredicateStatement
        (fun _ => True)) :
    theorem21LeftFactorReturnTwoDegreeStatement :=
  theorem21LeftFactorReturnRelation_of_predicate_true
    (R := fun m n => m = n + 2) htwo

/-- The unrestricted two-degree factor-return target is the `P := True` case
of the predicate-restricted target. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_true_of_twoDegree
    (htwo : theorem21LeftFactorReturnTwoDegreeStatement) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement (fun _ => True) :=
  theorem21LeftFactorReturnPredicateRelation_true_of_relation
    (R := fun m n => m = n + 2) htwo

/-- The sign-normalized positive-split subtraction-family leaf gives the
original two-degree factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_xSub
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeStatement :=
  theorem21LeftFactorReturnTwoDegree_of_predicate_true
    (theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
      (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_true_of_xSub
        hsub))

/-- Constant-right endpoint package for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_zero :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n = 0) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero

/-- Degree-one-right endpoint package for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_one :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one

/-- Low-degree right endpoint package for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_le_one :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 1) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one

/-- Constant-right-endpoint base case for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-one-right-endpoint case for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Low-degree right-endpoint cases for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 1) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the original two-degree left
factor-return leaf, packaged as a predicate-restricted statement. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_le_two :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two

/-- Degree-two-right endpoint package for the original two-degree left
factor-return leaf, modulo the normalized monic arithmetic leaf. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
      hmono)

/-- Degree-two-right endpoint package for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_two :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two

/-- Degree-two-right endpoint case for the original two-degree left
factor-return leaf, modulo the normalized monic arithmetic leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-two-right endpoint case for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 2) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree two for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 2) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right endpoint package for the original two-degree left
factor-return leaf, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
      hmono)

/-- Degree-three-right endpoint package for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_three :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_three_of_monic
    xSubQuarticCubicSplits

/-- Endpoint cases through right degree three for the original two-degree left
factor-return leaf, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate
    (positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Endpoint cases through right degree three for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegreePredicate_of_right_le_three :
    theorem21LeftFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnTwoDegreePredicate_of_right_le_three_of_monic
    xSubQuarticCubicSplits

/-- Degree-three-right endpoint case for the original two-degree left
factor-return leaf, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Degree-three-right endpoint case for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 3) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the original two-degree left
factor-return leaf, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    (positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono)
    hf hg hsgn hleft hdeg hcommon hgdeg

/-- Endpoint cases through right degree three for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree ≤ 3) :
    Compatible f g :=
  theorem21LeftFactorReturnTwoDegree_of_xSubPredicate
    positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three
    hf hg hsgn hleft hdeg hcommon hgdeg
end LiuOppositeSigns
end RealRooted
