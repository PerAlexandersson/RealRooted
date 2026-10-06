import RealRooted.LiuOppositeSigns.Theorem21Statements.CommonRootDeletion
import RealRooted.LiuOppositeSigns.Theorem21Statements.NoCommonCrossing

/-!
# The published forward direction of Liu Theorem 2.1 is false

The published statement of Liu Theorem 2.1 omits the common-root branch.  Its
forward direction fails already for `X` and `-(X ^ 2)`.  The corrected
theorem is `compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant`.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The nonconstant forward half of the published Liu Theorem 2.1, without the
common-root branch, is false when the endpoints share their largest root. The
minimal counterexample is `X` and `-(X ^ 2)`. -/
theorem not_forall_theorem21RootCountBranches_of_compatible_nonconstant :
    ¬ ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        f.natDegree ≠ 0 → g.natDegree ≠ 0 →
          Compatible f g → theorem21RootCountBranches f g := by
  intro hforward
  have hbase : Compatible (1 : ℝ[X]) (-X) :=
    Compatible.of_allComboRealRooted <|
      (allComboRealRooted_of_natDegree_le_one
        hasPosLeadingCoeff_one
        (by unfold HasPosLeadingCoeff; simp)
        (by simp) (by simp)).neg_right
  have hgsplits : (-(X ^ 2) : ℝ[X]).Splits := by
    simpa only [pow_two] using
      (Polynomial.Splits.X.mul Polynomial.Splits.X).neg
  have hcompat : Compatible (X : ℝ[X]) (-(X ^ 2)) := by
    simpa [pow_two] using
      hbase.mul_common_factor
        (d := (X : ℝ[X])) Polynomial.Splits.X
  have hsgn : OppositeLeadingSigns (X : ℝ[X]) (-(X ^ 2)) := by norm_num [OppositeLeadingSigns]
  have hfdeg : (X : ℝ[X]).natDegree ≠ 0 := by simp
  have hgdeg : (-(X ^ 2) : ℝ[X]).natDegree ≠ 0 := by
    norm_num [Polynomial.natDegree_neg, Polynomial.natDegree_pow]
  obtain ⟨r, s, hleft | hright⟩ :=
    hforward
      (f := (X : ℝ[X])) (g := -(X ^ 2))
      Polynomial.Splits.X hgsplits hsgn hfdeg hgdeg hcompat
  · have hgap :=
      hleft.count.natDegree_abs_sub_le_one
        (deleteRootFactor_splits_of_isRoot
          Polynomial.Splits.X hleft.f_largest.isRoot)
        hgsplits
    norm_num [natDegree_deleteRootFactor, Polynomial.natDegree_neg,
      Polynomial.natDegree_pow] at hgap
  · have hr : r = 0 := by simpa [Polynomial.IsRoot.def] using hright.f_largest.isRoot
    have hs : s = 0 := by simpa [Polynomial.IsRoot.def] using hright.g_largest.isRoot
    have hfalse : (0 : ℝ) < 0 := by simpa [hr, hs] using hright.largest_lt
    exact (lt_irrefl 0) hfalse

end LiuOppositeSigns
end RealRooted
