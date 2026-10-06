import RealRooted.LiuOppositeSigns.FactorReturnLeft
import RealRooted.LiuOppositeSigns.FactorReturnTwoDegree
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount

/-!
# Liu reverse direction by factor return

A Liu root-count branch deletes the largest root of one endpoint.  The deleted
pair then has degrees differing by at most one, so the restored pair falls in
one of three degree cases.  In each case the translated positive right pencil
splits, which restores compatibility of the original pair.  The right branch
follows from the left branch by symmetry.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- A left Liu root-count branch gives compatibility. -/
theorem LeftRootCountBranch.compatible {f g : ℝ[X]} {r s : ℝ}
    (hleft : LeftRootCountBranch f g r s)
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g := by
  have hright :
      ∀ μ : ℝ, 0 < μ →
        (X * (deleteRootFactor f r).comp (X + C r) +
            C μ * g.comp (X + C r)).Splits := by
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact theorem21LeftFactorReturnSameDegreeTranslatedRightFamily
        hf hg hsgn hleft hdeg
    · exact theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily
        hf hg hsgn hleft hdeg
    · exact theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily
        hf hg hsgn hleft hdeg
  exact hleft.compatible_of_translated_restore
    (theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
      hf hg hsgn hleft hright)

/-- A right Liu root-count branch gives compatibility. -/
theorem RightRootCountBranch.compatible {f g : ℝ[X]} {r s : ℝ}
    (hright : RightRootCountBranch f g r s)
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g :=
  (hright.toLeftBranch_symm.compatible hg hf hsgn.symm).comm

/-- Reverse direction of Liu Theorem 2.1: either root-count branch gives
compatibility of an opposite-leading-sign pair of real-rooted polynomials. -/
theorem compatible_of_theorem21RootCountBranches {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g := by
  rcases hbranches with ⟨r, s, hleft | hright⟩
  · exact hleft.compatible hf hg hsgn
  · exact hright.compatible hf hg hsgn

end LiuOppositeSigns
end RealRooted
