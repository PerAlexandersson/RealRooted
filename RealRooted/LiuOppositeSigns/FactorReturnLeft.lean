import RealRooted.LiuOppositeSigns.DeletionBranches
import RealRooted.LiuOppositeSigns.XSub.QuadraticCubic
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RightSuccessor
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SameDegree

/-!
# Liu left factor return: same- and successor-degree cases

In a left Liu branch the largest root `r` of `f` is deleted.  After translating
`r` to the origin and restoring the deleted factor as `X`, compatibility of the
restored pair follows once every positive right combination splits.  In the
same-degree and successor-degree cases these combinations are the
positive-split x-subtraction pencils.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- For a left Liu branch, if every positive right combination of the
translated restored pair splits, then that pair is compatible. -/
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

/-- Same-degree left Liu branch: after translating the deleted largest root of
`f` to the origin, every positive right combination of the restored pair
splits.  The sign-normalized deletion pair has right endpoint one degree
higher, so this is the right-successor x-subtraction pencil. -/
theorem theorem21LeftFactorReturnSameDegreeTranslatedRightFamily
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree) :
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
    have hsplit :=
      positiveSplitRightSuccDegreeTranslatedXSubRightFamily r hpair hqnn hGnn
        hdeg_pos μ hμ
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
      positiveSplitRightSuccDegreeTranslatedXSubRightFamily r hpair hQnn hgnn
        hdeg_pos μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

/-- Successor-degree left Liu branch: after translating the deleted largest
root of `f` to the origin, every positive right combination of the restored
pair splits.  The sign-normalized deletion pair has equal endpoint degrees, so
this is the same-degree x-subtraction pencil. -/
theorem theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 1) :
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
    have hsplit :=
      positiveSplitSameDegreeTranslatedXSubRightFamily r hpair hqnn hGnn
        hdeg_pos μ hμ
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
      positiveSplitSameDegreeTranslatedXSubRightFamily r hpair hQnn hgnn
        hdeg_pos μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

end LiuOppositeSigns
end RealRooted
