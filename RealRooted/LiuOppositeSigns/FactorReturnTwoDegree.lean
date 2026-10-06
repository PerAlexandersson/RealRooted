import RealRooted.LiuOppositeSigns.DeletionBranches
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.LeftSuccessor

/-!
# Liu left factor return: two-degree case

In a left Liu branch where `f` has degree two more than `g`, the
sign-normalized deletion pair has left endpoint one degree higher.  After
translating the deleted largest root to the origin, the positive right
combinations of the restored pair are left-successor x-subtraction pencils.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Two-degree left Liu branch: after translating the deleted largest root of
`f` to the origin, every positive right combination of the restored pair
splits. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2) :
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
    have hsplit :=
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily r hpair hqnn hGnn
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
        (-(deleteRootFactor f r)).natDegree = g.natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hsplit :=
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily r hpair hQnn hgnn
        hdeg_pos μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

end LiuOppositeSigns
end RealRooted
