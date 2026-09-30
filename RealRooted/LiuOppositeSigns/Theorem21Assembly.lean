import RealRooted.LiuOppositeSigns.FactorReturnAssembly

/-!
# Liu theorem reverse root-count assembly

This module contains the reverse root-count assembly layer for Liu Theorem 2.1,
including predicate-restricted branch packages and the current low-endpoint
reverse routes.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Predicate-restricted Liu root-count branch data.  The predicate is imposed
on the lower-degree endpoint selected by the branch. -/
def theorem21RootCountBranchesPredicate (P : ℕ → Prop) (f g : ℝ[X]) :
    Prop :=
  ∃ r s,
    (LeftRootCountBranch f g r s ∧ P g.natDegree) ∨
      (RightRootCountBranch f g r s ∧ P f.natDegree)

theorem theorem21RootCountBranchesPredicate_of_left
    {P : ℕ → Prop} {f g : ℝ[X]} {r s : ℝ}
    (hleft : LeftRootCountBranch f g r s) (hP : P g.natDegree) :
    theorem21RootCountBranchesPredicate P f g :=
  ⟨r, s, Or.inl ⟨hleft, hP⟩⟩

theorem theorem21RootCountBranchesPredicate_of_right
    {P : ℕ → Prop} {f g : ℝ[X]} {r s : ℝ}
    (hright : RightRootCountBranch f g r s) (hP : P f.natDegree) :
    theorem21RootCountBranchesPredicate P f g :=
  ⟨r, s, Or.inr ⟨hright, hP⟩⟩

/-- Predicate-restricted Liu root-count branch data forgets to the ordinary
branch statement. -/
theorem theorem21RootCountBranches_of_predicate
    {P : ℕ → Prop} {f g : ℝ[X]}
    (h : theorem21RootCountBranchesPredicate P f g) :
    theorem21RootCountBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact theorem21RootCountBranches_of_left hleft.1
  · exact theorem21RootCountBranches_of_right hright.1

/-- The unrestricted branch statement is the `P := True` case of the
predicate-restricted branch statement. -/
theorem theorem21RootCountBranchesPredicate_true_iff {f g : ℝ[X]} :
    theorem21RootCountBranchesPredicate (fun _ => True) f g ↔
      theorem21RootCountBranches f g := by
  constructor
  · exact theorem21RootCountBranches_of_predicate
  · intro h
    rcases h with ⟨r, s, hleft | hright⟩
    · exact theorem21RootCountBranchesPredicate_of_left hleft trivial
    · exact theorem21RootCountBranchesPredicate_of_right hright trivial

/-- Predicate-restricted reverse half of Liu Theorem 2.1.  The predicate is
attached to the lower-degree endpoint in the selected branch. -/
def theorem21RootCountBranchesToCompatiblePredicateStatement
    (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranchesPredicate P f g → Compatible f g

/-- Predicate-restricted nonconstant reverse half of Liu Theorem 2.1. -/
def theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
    (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranchesPredicate P f g → Compatible f g

/-- Predicate-restricted factor-return proves the predicate-restricted reverse
root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    {P : ℕ → Prop}
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P := by
  intro f g hf hg hsgn hbranches
  rcases hbranches with ⟨r, s, hleft | hright⟩
  · exact (hreturn hf hg hsgn).1 hleft.1
      (hleft.1.deletePairHasCommonInterleaver hsgn hf hg) hleft.2
  · exact (hreturn hf hg hsgn).2 hright.1
      (hright.1.deletePairHasCommonInterleaver hsgn hf hg) hright.2

/-- Bundled predicate-restricted positive-split x-subtraction case packages
prove the corresponding predicate-restricted reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_xSubCasePackage hcases)

/-- A predicate-restricted reverse direction also gives the corresponding
nonconstant predicate-restricted reverse direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    {P : ℕ → Prop}
    (hreverse : theorem21RootCountBranchesToCompatiblePredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P := by
  intro f g hf hg hsgn _hf_deg _hg_deg hbranches
  exact hreverse hf hg hsgn hbranches

/-- Bundled predicate-restricted positive-split x-subtraction case packages
prove the corresponding nonconstant predicate-restricted reverse root-count
direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)

/-- The proved sign-normalized positive-split x-subtraction cases prove every
nonconstant predicate-restricted reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSub
    {P : ℕ → Prop} :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate

/-- A `P := True` predicate-restricted nonconstant reverse direction gives the
ordinary nonconstant reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun _ => True)) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact hreverse hf hg hsgn hf_deg hg_deg
    (theorem21RootCountBranchesPredicate_true_iff.mpr hbranches)

/-- The proved sign-normalized positive-split x-subtraction cases prove the
nonconstant reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_xSub :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSub

end LiuOppositeSigns
end RealRooted
