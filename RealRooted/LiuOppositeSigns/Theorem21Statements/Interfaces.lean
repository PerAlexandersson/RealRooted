import RealRooted.LiuOppositeSigns.Theorem21Statements.CommonRootDeletion
import RealRooted.LiuOppositeSigns.Theorem21Statements.NoCommonCrossing

/-!
# Liu opposite-sign compatibility theorem interfaces

This module packages the theorem-shaped targets, corrected common-root branch,
and implication wrappers over the separate no-common and common-root engines.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Nonconstant forward half of Liu Theorem 2.1, isolated as a statement
target. -/
def theorem21CompatibleToRootCountBranchesNonconstantStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        Compatible f g → theorem21RootCountBranches f g

/-- The unreduced nonconstant forward statement is false when the endpoints
share their largest root. The minimal counterexample is `X` and `-(X ^ 2)`. -/
theorem not_theorem21CompatibleToRootCountBranchesNonconstantStatement :
    ¬ theorem21CompatibleToRootCountBranchesNonconstantStatement := by
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
      compatible_mul_common_factor
        (d := (X : ℝ[X])) Polynomial.Splits.X hbase
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

/-- Nonconstant reverse half of Liu Theorem 2.1, isolated as a statement
target. -/
def theorem21RootCountBranchesToCompatibleNonconstantStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranches f g → Compatible f g

/-- Nonconstant no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleRootCountNoCommonNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant forward half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        Compatible f g → theorem21RootCountBranches f g

end LiuOppositeSigns
end RealRooted
