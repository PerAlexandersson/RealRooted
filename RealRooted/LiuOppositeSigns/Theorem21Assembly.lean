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

/-- Predicate-restricted Liu branch data transports along endpoint predicate
implications. -/
theorem theorem21RootCountBranchesPredicate_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n) {f g : ℝ[X]}
    (hbranches : theorem21RootCountBranchesPredicate P f g) :
    theorem21RootCountBranchesPredicate Q f g := by
  rcases hbranches with ⟨r, s, hleft | hright⟩
  · exact theorem21RootCountBranchesPredicate_of_left hleft.1
      (hPQ _ hleft.2)
  · exact theorem21RootCountBranchesPredicate_of_right hright.1
      (hPQ _ hright.2)

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

/-- Predicate-restricted reverse directions transport along endpoint predicate
implications. -/
theorem theorem21RootCountBranchesToCompatiblePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RootCountBranchesToCompatiblePredicateStatement Q) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P := by
  intro f g hf hg hsgn hbranches
  exact hQ hf hg hsgn
    (theorem21RootCountBranchesPredicate_of_imp hPQ hbranches)

/-- Reassemble Liu Theorem 2.1 from separately proved forward and reverse
directions. -/
theorem theorem21CompatibleRootCount_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21CompatibleRootCountStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Predicate-restricted nonconstant reverse half of Liu Theorem 2.1. -/
def theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
    (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranchesPredicate P f g → Compatible f g

/-- Nonconstant predicate-restricted reverse directions transport along
endpoint predicate implications. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement Q) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact hQ hf hg hsgn hf_deg hg_deg
    (theorem21RootCountBranchesPredicate_of_imp hPQ hbranches)

/-- Reassemble the nonconstant Liu Theorem 2.1 statement from separately
proved forward and reverse directions. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement) :
    theorem21CompatibleRootCountNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact ⟨hforward hf hg hsgn hf_deg hg_deg,
    hreverse hf hg hsgn hf_deg hg_deg⟩

/-- The branch-retaining deletion-pair package reduces the reverse direction
of Liu Theorem 2.1 to the explicit factor-return principle. -/
theorem theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  exact theorem21DeletionPairCommonInterleaverBranchesToCompatible_of_factorReturn
    hreturn hf hg hsgn
    (theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
      hf hg hsgn hbranches)

/-- The factor-return principle proves the no-common-root reverse root-count
direction. -/
theorem
    theorem21RootCountBranchesToCompatibleNoCommon_of_deletionPairFactorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonStatement :=
  theorem21RootCountBranchesToCompatibleNoCommon_of_reverse
    (theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
      hreturn)

/-- The factor-return principle proves the reduced common-root reverse
direction. -/
theorem theorem21RootCountBranchesReducedToCompatible_of_factorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesReducedToCompatibleStatement :=
  theorem21RootCountBranchesReducedToCompatible_of_noCommonReverse
    (theorem21RootCountBranchesToCompatibleNoCommon_of_deletionPairFactorReturn
      hreturn)

/-- The no-common forward direction and factor-return principle assemble the
reduced common-root Liu target. -/
theorem theorem21CompatibleRootCountReduced_of_noCommonForward_and_factorReturn
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountReducedStatement :=
  theorem21CompatibleRootCountReduced_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesReduced_of_noCommonForward hforward)
    (theorem21RootCountBranchesReducedToCompatible_of_factorReturn hreturn)

/-- All-combinations factor-return proves the reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturnAllCombo
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21RootCountBranchesToCompatibleStatement :=
  theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- All-combinations factor-return degree cases prove the reverse root-count
direction. -/
theorem theorem21RootCountBranchesToCompatible_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleStatement :=
  theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases prove the reverse
root-count direction, with right cases supplied by symmetry. -/
theorem theorem21RootCountBranchesToCompatible_of_leftAllComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleStatement :=
  theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- A bundled sign-normalized positive-split x-subtraction case package proves
the reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatible_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleStatement :=
  theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- Sign-normalized positive-split x-subtraction cases prove the reverse
root-count direction. -/
theorem theorem21RootCountBranchesToCompatible_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21RootCountBranchesToCompatibleStatement :=
  theorem21RootCountBranchesToCompatible_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- The proved sign-normalized positive-split x-subtraction cases prove the
reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatible_of_xSub :
    theorem21RootCountBranchesToCompatibleStatement :=
  theorem21RootCountBranchesToCompatible_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCases

/-- Any reverse root-count direction restricts to endpoint predicate
subfamilies. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_reverse
    {P : ℕ → Prop}
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P := by
  intro f g hf hg hsgn hbranches
  exact hreverse hf hg hsgn
    (theorem21RootCountBranches_of_predicate hbranches)

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

/-- Endpoint factor-return case packages prove the corresponding
predicate-restricted reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
    {P : ℕ → Prop}
    (hcases : theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_endpointDegreeCases hcases)

/-- Left endpoint factor-return case packages prove the corresponding
predicate-restricted reverse root-count direction, with right cases supplied by
symmetry. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_leftEndpointCases hcases)

/-- Predicate-restricted translated compatibility case packages prove the
corresponding predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicate_of_translatedCompatibleCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_translatedCompatibleCasesPredicate
      hcases)

/-- Predicate-restricted translated right-family case packages prove the
corresponding predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicate_of_translatedRightFamilyCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_translatedRightFamilyCasesPredicate
      hcases)

/-- Predicate-restricted positive-split x-subtraction case packages prove the
corresponding predicate-restricted reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_xSubCases
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_xSubCasesPredicate
      hrightSucc hsame hleftSucc)

/-- Bundled predicate-restricted positive-split x-subtraction case packages
prove the corresponding predicate-restricted reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_xSubCasePackage hcases)

/-- The proved sign-normalized positive-split x-subtraction cases prove every
predicate-restricted reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_xSub
    {P : ℕ → Prop} :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate

/-- The unrestricted factor-return principle proves every predicate-restricted
reverse root-count direction by forgetting the endpoint predicate. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturn
    {P : ℕ → Prop}
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21DeletionPairCommonInterleaverFactorReturnPredicate_of_factorReturn
      hreturn)

/-- All-combinations factor-return proves every predicate-restricted reverse
root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnAllCombo
    {P : ℕ → Prop}
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- All-combinations factor-return degree cases prove every predicate-restricted
reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_allComboDegreeCases
    {P : ℕ → Prop}
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases prove every
predicate-restricted reverse root-count direction, with right cases supplied by
symmetry. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_leftAllComboCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatiblePredicateStatement P :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- A `P := True` predicate-restricted reverse direction gives the ordinary
reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatible_of_predicate_true
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun _ => True)) :
    theorem21RootCountBranchesToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  exact hreverse hf hg hsgn
    (theorem21RootCountBranchesPredicate_true_iff.mpr hbranches)

/-- Predicate-`True` reverse root-count direction is equivalent to the
ordinary reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_true_iff :
    theorem21RootCountBranchesToCompatiblePredicateStatement
      (fun _ => True) ↔ theorem21RootCountBranchesToCompatibleStatement :=
  ⟨theorem21RootCountBranchesToCompatible_of_predicate_true,
    theorem21RootCountBranchesToCompatiblePredicate_of_reverse⟩

/-- Predicate-`True` factor-return proves the ordinary reverse root-count
direction. -/
theorem
    theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturnPredicate_true
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21RootCountBranchesToCompatibleStatement :=
  theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true
      hreturn)

/-- A predicate-restricted reverse direction also gives the corresponding
nonconstant predicate-restricted reverse direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    {P : ℕ → Prop}
    (hreverse : theorem21RootCountBranchesToCompatiblePredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P := by
  intro f g hf hg hsgn _hf_deg _hg_deg hbranches
  exact hreverse hf hg hsgn hbranches

/-- Predicate-restricted factor-return proves the nonconstant
predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_deletionPairFactorReturnPredicate
    {P : ℕ → Prop}
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
      hreturn)

/-- Endpoint factor-return case packages prove the corresponding nonconstant
predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
    {P : ℕ → Prop}
    (hcases : theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)

/-- Left endpoint factor-return case packages prove the corresponding
nonconstant predicate-restricted reverse root-count direction, with right cases
supplied by symmetry. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
      hcases)

/-- Predicate-restricted translated compatibility case packages prove the
corresponding nonconstant predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_translatedCompatibleCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_translatedCompatibleCases
      hcases)

/-- Predicate-restricted translated right-family case packages prove the
corresponding nonconstant predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_translatedRightFamilyCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_translatedRightFamilyCases
      hcases)

/-- Predicate-restricted positive-split x-subtraction case packages prove the
corresponding nonconstant predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCases
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCases
      hrightSucc hsame hleftSucc)

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

/-- The unrestricted factor-return principle proves every nonconstant
predicate-restricted reverse root-count direction by forgetting the endpoint
predicate. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_deletionPairFactorReturn
    {P : ℕ → Prop}
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturn
      hreturn)

/-- All-combinations factor-return proves every nonconstant
predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_deletionPairFactorReturnAllCombo
    {P : ℕ → Prop}
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnAllCombo
      hreturn)

/-- All-combinations factor-return degree cases prove every nonconstant
predicate-restricted reverse root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_allComboDegreeCases
    {P : ℕ → Prop}
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases prove every nonconstant
predicate-restricted reverse root-count direction, with right cases supplied
by symmetry. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftAllComboCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement P :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftAllComboCases
      hcases)

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

/-- Predicate-`True` factor-return proves the ordinary nonconstant reverse
root-count direction. -/
theorem
    theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturnPredicate_true
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_deletionPairFactorReturnPredicate
      hreturn)

/-- The proved sign-normalized positive-split x-subtraction cases prove the
nonconstant reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_xSub :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSub

/-- The isolated forward direction plus the proved x-subtraction reverse route
give Liu Theorem 2.1 in root-count form. -/
theorem theorem21CompatibleRootCount_of_forward_and_xSub
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_forward_and_reverse hforward
    theorem21RootCountBranchesToCompatible_of_xSub

/-- The no-common forward direction plus the proved x-subtraction reverse route
give the reduced common-root Liu Theorem 2.1 statement in root-count form. -/
theorem theorem21CompatibleRootCountReduced_of_noCommonForward_and_xSub
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleRootCountReducedStatement :=
  theorem21CompatibleRootCountReduced_of_noCommon_forward_and_reverse hforward
    (theorem21RootCountBranchesToCompatibleNoCommon_of_reverse
      theorem21RootCountBranchesToCompatible_of_xSub)

/-- The no-common forward direction plus the proved x-subtraction reverse route
give the corrected common-root-branch Liu Theorem 2.1 statement in root-count
form. -/
theorem theorem21CompatibleRootCountWithCommon_of_noCommonForward_and_xSub
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleRootCountWithCommonStatement :=
  theorem21CompatibleRootCountWithCommon_of_noCommonForward_and_reverse hforward
    theorem21RootCountBranchesToCompatible_of_xSub

/-- The isolated nonconstant forward direction plus the proved x-subtraction
reverse route give the nonconstant Liu Theorem 2.1 statement in root-count
form. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_xSub
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_forward_and_reverse hforward
    theorem21RootCountBranchesToCompatibleNonconstant_of_xSub

/-- Liu Theorem 2.1 follows from the isolated forward direction and a
predicate-`True` reverse direction. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_predicate_true
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranches_of_commonForward hforward)
    (theorem21RootCountBranchesToCompatible_of_predicate_true hreverse)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
a predicate-`True` reverse direction. -/
theorem theorem21CompatibleRootCount_of_forward_and_predicate_true
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_predicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreverse

/-- Liu Theorem 2.1 follows from the isolated forward root-count direction and
the deletion-pair factor-return principle. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_deletionPairCommonInterleaverIff
    (theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_factorReturn
      hforward hreturn)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
the deletion-pair factor-return principle. -/
theorem theorem21CompatibleRootCount_of_forward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- Liu Theorem 2.1 follows from the isolated forward direction and an
all-combinations factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnAllCombo
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
an all-combinations factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_forward_and_deletionPairFactorReturnAllCombo
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnAllCombo
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- Liu Theorem 2.1 follows from the isolated forward direction and
all-combinations factor-return degree cases. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
all-combinations factor-return degree cases. -/
theorem theorem21CompatibleRootCount_of_forward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_allComboDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Liu Theorem 2.1 follows from the isolated forward direction and left
all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_leftAllComboCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
left all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem theorem21CompatibleRootCount_of_forward_and_leftAllComboCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_leftAllComboCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Liu Theorem 2.1 follows from the isolated forward direction and a bundled
sign-normalized positive-split x-subtraction case package. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
a bundled sign-normalized positive-split x-subtraction case package. -/
theorem theorem21CompatibleRootCount_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Liu Theorem 2.1 follows from the isolated forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_xSubCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem theorem21CompatibleRootCount_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- Liu Theorem 2.1 follows from the isolated forward direction and a
predicate-`True` factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnPredicate_true
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true
      hreturn)

/-- Liu Theorem 2.1 follows from the isolated root-count forward direction and
a predicate-`True` factor-return principle. -/
theorem
    theorem21CompatibleRootCount_of_forward_and_deletionPairFactorReturnPredicate_true
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_commonForward_and_deletionPairFactorReturnPredicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreturn

/-- The deletion-pair factor-return principle also reduces the nonconstant
reverse direction of Liu Theorem 2.1. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_deletionPairFactorReturn
      hreturn)

/-- All-combinations factor-return proves the nonconstant reverse root-count
direction. -/
theorem
    theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturnAllCombo
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- All-combinations factor-return degree cases prove the nonconstant reverse
root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases prove the nonconstant
reverse root-count direction, with right cases supplied by symmetry. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_leftAllComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- A bundled sign-normalized positive-split x-subtraction case package proves
the nonconstant reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- Sign-normalized positive-split x-subtraction cases prove the nonconstant
reverse root-count direction. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and a predicate-`True` nonconstant reverse direction. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_predicate_true
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesNonconstant_of_commonForward
      hforward)
    (theorem21RootCountBranchesToCompatibleNonconstant_of_predicate_true
      hreverse)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and a predicate-`True` nonconstant
reverse direction. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_predicate_true
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_predicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreverse

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and the deletion-pair factor-return principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_deletionPairCommonInterleaverIff
    (theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_factorReturn
      hforward hreturn)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and the deletion-pair factor-return
principle. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and an all-combinations factor-return principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturnAllCombo
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo hreturn)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and an all-combinations factor-return
principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_deletionPairFactorReturnAllCombo
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturnAllCombo
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and all-combinations factor-return degree cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_allComboDegreeCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
      hcases)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and all-combinations factor-return
degree cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_allComboDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and left all-combinations factor-return degree cases, with
right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_leftAllComboCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
      hcases)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and left all-combinations
factor-return degree cases, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_leftAllComboCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_leftAllComboCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated forward
direction and a bundled sign-normalized positive-split x-subtraction case
package. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCasePackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and a bundled sign-normalized
positive-split x-subtraction case package. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and sign-normalized positive-split x-subtraction cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and sign-normalized positive-split
x-subtraction cases. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and a predicate-`True` factor-return principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_factorReturnPredicate_true
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_deletionPairFactorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true
      hreturn)

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
nonconstant root-count forward direction and a predicate-`True` factor-return
principle. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_deletionPairFactorReturnPredicate_true
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_factorReturnPredicate_true
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreturn

/-- Current low-endpoint reverse route: same/succ left factor-return leaves
prove the reverse Liu direction for branches whose lower-degree endpoint has
degree at most two. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_sameSucc_and_endpoint_le_two
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement) :
    theorem21RootCountBranchesToCompatiblePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RootCountBranchesToCompatiblePredicate_of_deletionPairFactorReturnPredicate
    (theorem21FactorReturnPredicate_of_sameSucc_and_endpoint_le_two hsame hsucc)

/-- Current low-endpoint reverse route: Liu's reverse direction holds for
branches whose lower-degree endpoint has degree at most two. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_two :
    theorem21RootCountBranchesToCompatiblePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_two

/-- Endpoint-degree-two branch data for the current bounded Liu reverse route.
This is the predicate-restricted branch statement with predicate `n ≤ 2` on the
lower-degree endpoint. -/
def theorem21RootCountBranchesEndpointLeTwo (f g : ℝ[X]) : Prop :=
  theorem21RootCountBranchesPredicate (fun n => n ≤ 2) f g

/-- Left-branch constructor for endpoint-degree-two branch data. -/
theorem theorem21RootCountBranchesEndpointLeTwo_of_left
    {f g : ℝ[X]} {r s : ℝ} (hleft : LeftRootCountBranch f g r s)
    (hgdeg : g.natDegree ≤ 2) :
    theorem21RootCountBranchesEndpointLeTwo f g :=
  theorem21RootCountBranchesPredicate_of_left hleft hgdeg

/-- Right-branch constructor for endpoint-degree-two branch data. -/
theorem theorem21RootCountBranchesEndpointLeTwo_of_right
    {f g : ℝ[X]} {r s : ℝ} (hright : RightRootCountBranch f g r s)
    (hfdeg : f.natDegree ≤ 2) :
    theorem21RootCountBranchesEndpointLeTwo f g :=
  theorem21RootCountBranchesPredicate_of_right hright hfdeg

/-- Ordinary branch data becomes endpoint-degree-two branch data when both
endpoints have degree at most two. -/
theorem theorem21RootCountBranchesEndpointLeTwo_of_natDegree_le_two
    {f g : ℝ[X]} (hfdeg : f.natDegree ≤ 2) (hgdeg : g.natDegree ≤ 2)
    (hbranches : theorem21RootCountBranches f g) :
    theorem21RootCountBranchesEndpointLeTwo f g := by
  rcases hbranches with ⟨r, s, hleft | hright⟩
  · exact theorem21RootCountBranchesEndpointLeTwo_of_left hleft hgdeg
  · exact theorem21RootCountBranchesEndpointLeTwo_of_right hright hfdeg

/-- Low-endpoint reverse route: Liu's reverse direction holds for branches whose
lower-degree endpoint has degree at most two. -/
theorem theorem21RootCountBranchesToCompatible_of_endpoint_le_two :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g := by
  intro f g hf hg hsgn hbranches
  exact theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_two
    hf hg hsgn hbranches

/-- Low-degree endpoints turn the endpoint-degree-two reverse route into an
ordinary reverse implication. -/
theorem theorem21RootCountBranchesToCompatible_of_natDegree_le_two
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 2) (hgdeg : g.natDegree ≤ 2)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatible_of_endpoint_le_two hf hg hsgn
    (theorem21RootCountBranchesEndpointLeTwo_of_natDegree_le_two
      hfdeg hgdeg hbranches)

/-- Conditional low-endpoint reverse route: once the normalized quartic/cubic
arithmetic terminal is proved, Liu's reverse direction holds for branches whose
lower-degree endpoint has degree at most three. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21RootCountBranchesToCompatiblePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
    (positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
      hmono)

/-- Low-endpoint reverse route: Liu's reverse direction holds for branches
whose lower-degree endpoint has degree at most three. -/
theorem theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three :
    theorem21RootCountBranchesToCompatiblePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three

/-- Endpoint-degree-three branch data for the current bounded Liu reverse
route.  This is just the predicate-restricted branch statement with predicate
`n ≤ 3` on the lower-degree endpoint. -/
def theorem21RootCountBranchesEndpointLeThree (f g : ℝ[X]) : Prop :=
  theorem21RootCountBranchesPredicate (fun n => n ≤ 3) f g

/-- Bundled predicate-restricted x-subtraction cases prove the
endpoint-degree-three reverse route. -/
theorem theorem21RootCountBranchesToCompatible_of_endpoint_le_three_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn hbranches
  exact theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
    hcases hf hg hsgn hbranches

/-- Left-branch constructor for endpoint-degree-three branch data. -/
theorem theorem21RootCountBranchesEndpointLeThree_of_left
    {f g : ℝ[X]} {r s : ℝ} (hleft : LeftRootCountBranch f g r s)
    (hgdeg : g.natDegree ≤ 3) :
    theorem21RootCountBranchesEndpointLeThree f g :=
  theorem21RootCountBranchesPredicate_of_left hleft hgdeg

/-- Right-branch constructor for endpoint-degree-three branch data. -/
theorem theorem21RootCountBranchesEndpointLeThree_of_right
    {f g : ℝ[X]} {r s : ℝ} (hright : RightRootCountBranch f g r s)
    (hfdeg : f.natDegree ≤ 3) :
    theorem21RootCountBranchesEndpointLeThree f g :=
  theorem21RootCountBranchesPredicate_of_right hright hfdeg

/-- Ordinary branch data becomes endpoint-degree-three branch data when both
endpoints have degree at most three. -/
theorem theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
    {f g : ℝ[X]} (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hbranches : theorem21RootCountBranches f g) :
    theorem21RootCountBranchesEndpointLeThree f g := by
  rcases hbranches with ⟨r, s, hleft | hright⟩
  · exact theorem21RootCountBranchesEndpointLeThree_of_left hleft hgdeg
  · exact theorem21RootCountBranchesEndpointLeThree_of_right hright hfdeg

/-- Endpoint-degree-two branch data is a subcase of endpoint-degree-three branch
data. -/
theorem theorem21RootCountBranchesEndpointLeThree_of_endpoint_le_two
    {f g : ℝ[X]} :
    theorem21RootCountBranchesEndpointLeTwo f g →
      theorem21RootCountBranchesEndpointLeThree f g :=
  theorem21RootCountBranchesPredicate_of_imp fun _ hn =>
    hn.trans (by norm_num)

/-- Low-endpoint reverse route for explicit endpoint-degree-three branch data.
-/
theorem theorem21RootCountBranchesToCompatible_of_endpoint_le_three :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn hbranches
  exact theorem21RootCountBranchesToCompatible_of_endpoint_le_three_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three
    hf hg hsgn hbranches

/-- Bundled predicate-restricted x-subtraction cases prove the nonconstant
endpoint-degree-three reverse route. -/
theorem
    theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_three_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        f.natDegree ≠ 0 → g.natDegree ≠ 0 →
          theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
    hcases hf hg hsgn hf_deg hg_deg hbranches

/-- Nonconstant wrapper for the endpoint-degree-three reverse route. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_three :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        f.natDegree ≠ 0 → g.natDegree ≠ 0 →
          theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn _hf_deg _hg_deg hbranches
  exact
    theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_three_xSubCasePackage
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three
      hf hg hsgn _hf_deg _hg_deg hbranches

/-- Endpoint factor-return case packages prove the endpoint-degree-three
reverse route. -/
theorem theorem21RootCountBranchesToCompatible_of_endpointDegreeCases
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn hbranches
  exact theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
    hcases hf hg hsgn hbranches

/-- Left endpoint factor-return case packages prove the endpoint-degree-three
reverse route, with right cases supplied by symmetry. -/
theorem theorem21RootCountBranchesToCompatible_of_leftEndpointCases
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn hbranches
  exact theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
    hcases hf hg hsgn hbranches

/-- Endpoint factor-return case packages prove the nonconstant
endpoint-degree-three reverse route. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_endpointDegreeCases
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        f.natDegree ≠ 0 → g.natDegree ≠ 0 →
          theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
    hcases hf hg hsgn hf_deg hg_deg hbranches

/-- Left endpoint factor-return case packages prove the nonconstant
endpoint-degree-three reverse route, with right cases supplied by symmetry. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_leftEndpointCases
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        f.natDegree ≠ 0 → g.natDegree ≠ 0 →
          theorem21RootCountBranchesEndpointLeThree f g → Compatible f g := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
    hcases hf hg hsgn hf_deg hg_deg hbranches

/-- Low-degree endpoints turn the current endpoint-degree-three reverse route
into an ordinary reverse implication. -/
theorem theorem21RootCountBranchesToCompatible_of_natDegree_le_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatible_of_endpoint_le_three hf hg hsgn
    (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
      hfdeg hgdeg hbranches)

/-- Nonconstant wrapper for the low-degree ordinary reverse implication. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_three
    hf hg hsgn hfdeg_ne hgdeg_ne
    (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
      hfdeg_le hgdeg_le hbranches)

/-- Endpoint factor-return case packages give the low-degree ordinary reverse
implication. -/
theorem theorem21RootCountBranchesToCompatible_of_natDegree_le_three_endpointDegreeCases
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatible_of_endpointDegreeCases
    hcases hf hg hsgn
    (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
      hfdeg hgdeg hbranches)

/-- Left endpoint factor-return case packages give the low-degree ordinary
reverse implication, with right cases supplied by symmetry. -/
theorem theorem21RootCountBranchesToCompatible_of_natDegree_le_three_leftEndpointCases
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatible_of_leftEndpointCases
    hcases hf hg hsgn
    (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
      hfdeg hgdeg hbranches)

/-- Endpoint factor-return case packages give the low-degree nonconstant
ordinary reverse implication. -/
theorem
    theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_three_endpointDegreeCases
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_endpointDegreeCases
    hcases hf hg hsgn hfdeg_ne hgdeg_ne
    (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
      hfdeg_le hgdeg_le hbranches)

/-- Left endpoint factor-return case packages give the low-degree nonconstant
ordinary reverse implication, with right cases supplied by symmetry. -/
theorem
    theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_three_leftEndpointCases
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_leftEndpointCases
    hcases hf hg hsgn hfdeg_ne hgdeg_ne
    (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
      hfdeg_le hgdeg_le hbranches)

/-- Degree-case-aware low-endpoint branch data for the current reverse Liu route.
The same-degree and successor-degree branches are available through endpoint
degree three, while the two-degree-gap branch is available through endpoint
degree two. -/
def theorem21RootCountBranchesEndpointLeThreeTwo (f g : ℝ[X]) :
    Prop :=
  ∃ r s,
    (LeftRootCountBranch f g r s ∧
        ((f.natDegree = g.natDegree ∧ g.natDegree ≤ 3) ∨
          (f.natDegree = g.natDegree + 1 ∧ g.natDegree ≤ 3) ∨
            (f.natDegree = g.natDegree + 2 ∧ g.natDegree ≤ 2))) ∨
      (RightRootCountBranch f g r s ∧
        ((g.natDegree = f.natDegree ∧ f.natDegree ≤ 3) ∨
          (g.natDegree = f.natDegree + 1 ∧ f.natDegree ≤ 3) ∨
            (g.natDegree = f.natDegree + 2 ∧ f.natDegree ≤ 2)))

/-- The older endpoint-`3,2` branch package is a subcase of the uniform
endpoint-degree-three package. -/
theorem theorem21RootCountBranchesEndpointLeThree_of_endpoint_le_three_two
    {f g : ℝ[X]} :
    theorem21RootCountBranchesEndpointLeThreeTwo f g →
      theorem21RootCountBranchesEndpointLeThree f g := by
  intro hbranches
  rcases hbranches with ⟨r, s, hleft | hright⟩
  · rcases hleft with ⟨hleft, hcase⟩
    rcases hcase with hsame | hsucc | htwo
    · exact theorem21RootCountBranchesEndpointLeThree_of_left hleft hsame.2
    · exact theorem21RootCountBranchesEndpointLeThree_of_left hleft hsucc.2
    · exact theorem21RootCountBranchesEndpointLeThree_of_left hleft
        (htwo.2.trans (by norm_num))
  · rcases hright with ⟨hright, hcase⟩
    rcases hcase with hsame | hsucc | htwo
    · exact theorem21RootCountBranchesEndpointLeThree_of_right hright hsame.2
    · exact theorem21RootCountBranchesEndpointLeThree_of_right hright hsucc.2
    · exact theorem21RootCountBranchesEndpointLeThree_of_right hright
        (htwo.2.trans (by norm_num))

/-- Current degree-case-aware low-endpoint reverse route: Liu's reverse
direction holds for same/succ branches through endpoint degree three and
two-degree-gap branches through endpoint degree two. -/
theorem theorem21RootCountBranchesToCompatible_of_endpoint_le_three_two :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        theorem21RootCountBranchesEndpointLeThreeTwo f g → Compatible f g := by
  intro f g hf hg hsgn hbranches
  exact theorem21RootCountBranchesToCompatible_of_endpoint_le_three
    hf hg hsgn
    (theorem21RootCountBranchesEndpointLeThree_of_endpoint_le_three_two
      hbranches)

/-- Nonconstant wrapper for the degree-case-aware low-endpoint reverse route. -/
theorem
    theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_three_two :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        f.natDegree ≠ 0 → g.natDegree ≠ 0 →
          theorem21RootCountBranchesEndpointLeThreeTwo f g → Compatible f g := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_three
    hf hg hsgn hf_deg hg_deg
    (theorem21RootCountBranchesEndpointLeThree_of_endpoint_le_three_two
      hbranches)

/-- Current low-endpoint nonconstant reverse route. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_sameSucc_and_endpoint_le_two
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
      (fun n => n ≤ 2) :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_sameSucc_and_endpoint_le_two
      hsame hsucc)

/-- Current low-endpoint nonconstant reverse route, with all degree branches
closed through endpoint degree two. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_two :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
      (fun n => n ≤ 2) :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_two

/-- Nonconstant wrapper for the endpoint-degree-two reverse route. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_two :
    ∀ {f g : ℝ[X]},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        f.natDegree ≠ 0 → g.natDegree ≠ 0 →
          theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g := by
  intro f g hf hg hsgn hf_deg hg_deg hbranches
  exact theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_two
    hf hg hsgn hf_deg hg_deg hbranches

/-- Nonconstant wrapper for the low-degree endpoint-degree-two reverse
implication. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_two
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 2) (hgdeg_le : g.natDegree ≤ 2)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_two
    hf hg hsgn hfdeg_ne hgdeg_ne
    (theorem21RootCountBranchesEndpointLeTwo_of_natDegree_le_two
      hfdeg_le hgdeg_le hbranches)

/-- Conditional low-endpoint nonconstant reverse route through endpoint degree
three, modulo the normalized monic quartic/cubic arithmetic leaf. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
      (fun n => n ≤ 3) :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three_of_monic
      hmono)

/-- Low-endpoint nonconstant reverse route through endpoint degree three. -/
theorem
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three :
    theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
      (fun n => n ≤ 3) :=
  theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_predicate
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three

end LiuOppositeSigns
end RealRooted
