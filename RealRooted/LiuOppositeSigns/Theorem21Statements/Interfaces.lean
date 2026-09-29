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

/-- Full unreduced target for Liu Theorem 2.1, stated against the project's
`Compatible` predicate.  The two branch predicate below is the no-common
largest-root case split, so proving this full statement also requires a
common-root reduction outside the branch predicate.  For the theorem shape
matching Liu's reduced proof stage, use
`theorem21CompatibleRootCountNoCommonStatement`.  For an explicit tracker for
the missing common-root interface, see GitHub issue #98.

for two real-rooted polynomials with opposite leading signs, compatibility is
equivalent to the appropriate largest-root deletion branch satisfying Liu's
closed-at-or-above root-count condition. -/
def theorem21CompatibleRootCountStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant form of Liu Theorem 2.1.  This is the induction-friendly
version of the statement because the root-count branches delete a largest root
from each polynomial. -/
def theorem21CompatibleRootCountNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Forward half of Liu Theorem 2.1, isolated as a statement target. -/
def theorem21CompatibleToRootCountBranchesStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21RootCountBranches f g

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

/-- Reverse half of Liu Theorem 2.1, isolated as a statement target. -/
def theorem21RootCountBranchesToCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranches f g → Compatible f g

/-- Nonconstant reverse half of Liu Theorem 2.1, isolated as a statement
target. -/
def theorem21RootCountBranchesToCompatibleNonconstantStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranches f g → Compatible f g

/-- No-common-root form of Liu Theorem 2.1, matching the reduced case in the
paper's proof. -/
def theorem21CompatibleRootCountNoCommonStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleRootCountNoCommonNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Forward half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleToRootCountBranchesNoCommonStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → Compatible f g → theorem21RootCountBranches f g

/-- Nonconstant forward half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        Compatible f g → theorem21RootCountBranches f g

/-- Reverse half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21RootCountBranchesToCompatibleNoCommonStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → theorem21RootCountBranches f g → Compatible f g

/-- Nonconstant reverse half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranches f g → Compatible f g

/-- Reduced common-root Liu target.  The ordinary branch keeps the
no-common-root witness needed by no-common reverse theorems. -/
def theorem21CompatibleRootCountReducedStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranchesReduced f g)

/-- Forward half of the reduced common-root target. -/
def theorem21CompatibleToRootCountBranchesReducedStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21RootCountBranchesReduced f g

/-- Reverse half of the reduced common-root target. -/
def theorem21RootCountBranchesReducedToCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranchesReduced f g → Compatible f g

/-- Unreduced theorem target with an explicit common-root branch.  This is the
safe full-statement interface; the older `theorem21CompatibleRootCountStatement`
remains the branch-only target used by existing conditional wrappers. -/
def theorem21CompatibleRootCountWithCommonStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranchesWithCommon f g)

/-- Forward half of the corrected common-root-branch target. -/
def theorem21CompatibleToRootCountBranchesWithCommonStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21RootCountBranchesWithCommon f g

/-- Reverse half of the corrected common-root-branch target. -/
def theorem21RootCountBranchesWithCommonToCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranchesWithCommon f g → Compatible f g

/-- The paper-shaped statement implies its nonconstant restriction. -/
theorem theorem21CompatibleRootCountNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  fun f g hf hg hsgn _ _ => h f g hf hg hsgn

/-- The unreduced full statement implies the no-common-root restriction. -/
theorem theorem21CompatibleRootCountNoCommon_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleRootCountNoCommonStatement :=
  fun f g hf hg hsgn _hno => h f g hf hg hsgn

/-- The unreduced nonconstant statement implies the nonconstant no-common-root
restriction. -/
theorem
    theorem21CompatibleRootCountNoCommonNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    theorem21CompatibleRootCountNoCommonNonconstantStatement :=
  fun f g hf hg hsgn _hno hf_deg hg_deg => h f g hf hg hsgn hf_deg hg_deg

/-- The no-common-root statement implies its nonconstant restriction. -/
theorem
    theorem21CompatibleRootCountNoCommonNonconstant_of_theorem21CompatibleRootCountNoCommon
    (h : theorem21CompatibleRootCountNoCommonStatement) :
    theorem21CompatibleRootCountNoCommonNonconstantStatement :=
  fun f g hf hg hsgn hno _ _ => h f g hf hg hsgn hno

/-- The corrected common-root-branch statement implies its branch-only
restriction in the no-common regime. -/
theorem theorem21CompatibleRootCountNoCommon_of_theorem21CompatibleRootCountWithCommon
    (h : theorem21CompatibleRootCountWithCommonStatement) :
    theorem21CompatibleRootCountNoCommonStatement := by
  intro f g hf hg hsgn hno
  constructor
  · intro hcompat
    rcases (h f g hf hg hsgn).1 hcompat with hbranches | hcommon
    · exact hbranches
    · rcases hcommon with ⟨r, hfr, hgr, _hcompat⟩
      exact False.elim ((hno r hfr) hgr)
  · intro hbranches
    exact (h f g hf hg hsgn).2 (Or.inl hbranches)

/-- Projection form of `theorem21CompatibleRootCountStatement`. -/
theorem compatible_iff_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn

/-- Projection form of the nonconstant Liu Theorem 2.1 statement. -/
theorem compatible_iff_theorem21RootCountBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn hf_deg hg_deg

/-- Projection form of the no-common-root Liu Theorem 2.1 statement. -/
theorem compatible_iff_theorem21RootCountBranches_noCommon
    (h : theorem21CompatibleRootCountNoCommonStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hno : NoCommonRoots f g) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn hno

/-- Projection form of the nonconstant no-common-root Liu statement. -/
theorem compatible_iff_theorem21RootCountBranches_noCommon_nonconstant
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn hno hf_deg hg_deg

/-- Forward half extracted from the paper-shaped Liu Theorem 2.1 statement. -/
theorem theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleToRootCountBranchesStatement := by
  intro f g hf hg hsgn
  exact (h f g hf hg hsgn).1

/-- Forward half extracted from the no-common-root Liu statement. -/
theorem theorem21CompatibleToRootCountBranchesNoCommon_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonStatement := by
  intro f g hf hg hsgn hno
  exact (h f g hf hg hsgn hno).1

/-- Forward half extracted from the nonconstant no-common-root Liu statement.
-/
theorem
    theorem21CompatibleToRootCountBranchesNoCommonNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hf_deg hg_deg
  exact (h f g hf hg hsgn hno hf_deg hg_deg).1

/-- Reverse half extracted from the paper-shaped Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21RootCountBranchesToCompatibleStatement := by
  intro f g hf hg hsgn
  exact (h f g hf hg hsgn).2

/-- Reverse half extracted from the nonconstant Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact (h f g hf hg hsgn hf_deg hg_deg).2

/-- Reverse half extracted from the no-common-root Liu statement. -/
theorem theorem21RootCountBranchesToCompatibleNoCommon_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonStatement := by
  intro f g hf hg hsgn hno
  exact (h f g hf hg hsgn hno).2

/-- Reverse half extracted from the nonconstant no-common-root Liu statement.
-/
theorem
    theorem21RootCountBranchesToCompatibleNoCommonNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hf_deg hg_deg
  exact (h f g hf hg hsgn hno hf_deg hg_deg).2

/-- The ordinary reverse half restricts to the nonconstant reverse half. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn _hf_deg _hg_deg hbranches
  exact hreverse hf hg hsgn hbranches

/-- The no-common-root forward half restricts to its nonconstant form. -/
theorem theorem21CompatibleToRootCountBranchesNoCommonNonconstant_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno _hf_deg _hg_deg hcompat
  exact hforward hf hg hsgn hno hcompat

/-- The ordinary forward half implies the no-common-root forward half. -/
theorem theorem21CompatibleToRootCountBranchesNoCommon_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonStatement := by
  intro f g hf hg hsgn _hno hcompat
  exact hforward hf hg hsgn hcompat

/-- The no-common-root reverse half restricts to its nonconstant form. -/
theorem theorem21RootCountBranchesToCompatibleNoCommonNonconstant_of_noCommonReverse
    (hreverse : theorem21RootCountBranchesToCompatibleNoCommonStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno _hf_deg _hg_deg hbranches
  exact hreverse hf hg hsgn hno hbranches

/-- The ordinary reverse half implies the no-common-root reverse half. -/
theorem theorem21RootCountBranchesToCompatibleNoCommon_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonStatement := by
  intro f g hf hg hsgn _hno hbranches
  exact hreverse hf hg hsgn hbranches

/-- The ordinary nonconstant reverse half implies the nonconstant
no-common-root reverse half. -/
theorem theorem21RootCountBranchesToCompatibleNoCommonNonconstant_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement := by
  intro f g hf hg hsgn _hno hf_deg hg_deg hbranches
  exact hreverse hf hg hsgn hf_deg hg_deg hbranches

/-- Projection form of the isolated forward direction of Liu Theorem 2.1. -/
theorem theorem21RootCountBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  hforward hf hg hsgn hcompat

/-- Projection form of the isolated no-common-root forward direction of
Liu Theorem 2.1. -/
theorem theorem21RootCountBranches_of_compatible_of_forward_noCommon
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  hforward hf hg hsgn hno hcompat

/-- Projection form of the isolated nonconstant no-common-root forward
direction of Liu Theorem 2.1. -/
theorem theorem21RootCountBranches_of_compatible_of_forward_noCommon_nonconstant
    (hforward :
      theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  hforward hf hg hsgn hno hf_deg hg_deg hcompat

/-- Forward direction of Liu Theorem 2.1 as a reusable projection. -/
theorem theorem21RootCountBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- Forward direction of the no-common-root Liu statement. -/
theorem theorem21RootCountBranches_of_compatible_noCommon
    (h : theorem21CompatibleRootCountNoCommonStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hno : NoCommonRoots f g) (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_of_forward_noCommon
    (theorem21CompatibleToRootCountBranchesNoCommon_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hno hcompat

/-- Forward direction of the nonconstant no-common-root Liu statement. -/
theorem theorem21RootCountBranches_of_compatible_noCommon_nonconstant
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_of_forward_noCommon_nonconstant
    (theorem21CompatibleToRootCountBranchesNoCommonNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hno hf_deg hg_deg hcompat

/-- The no-common-root forward direction plus common-root deletion gives the
reduced common-root branch predicate. -/
theorem theorem21RootCountBranchesReduced_of_compatible_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranchesReduced f g := by
  by_cases hno : NoCommonRoots f g
  · exact Or.inl ⟨hno, hforward hf hg hsgn hno hcompat⟩
  · exact Or.inr
      (CommonRootDeletionCompatibleBranch.of_compatible_of_not_noCommonRoots
        hcompat hno)

/-- The no-common-root forward direction plus common-root deletion gives the
corrected full forward direction with an explicit common-root branch. -/
theorem theorem21RootCountBranchesWithCommon_of_compatible_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranchesWithCommon f g := by
  exact theorem21RootCountBranchesReduced.withCommon
    (theorem21RootCountBranchesReduced_of_compatible_of_noCommonForward
      hforward hf hg hsgn hcompat)

/-- The corrected reduced forward direction follows from the no-common forward
direction and the automatic common-root deletion branch. -/
theorem theorem21CompatibleToRootCountBranchesReduced_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesReducedStatement := by
  intro f g hf hg hsgn hcompat
  exact theorem21RootCountBranchesReduced_of_compatible_of_noCommonForward
    hforward hf hg hsgn hcompat

/-- The reduced common-root branch predicate forgets to the existing
with-common branch predicate. -/
theorem theorem21CompatibleToRootCountBranchesWithCommon_of_reduced
    (hreduced : theorem21CompatibleToRootCountBranchesReducedStatement) :
    theorem21CompatibleToRootCountBranchesWithCommonStatement := by
  intro f g hf hg hsgn hcompat
  exact theorem21RootCountBranchesReduced.withCommon
    (hreduced hf hg hsgn hcompat)

/-- No-common-root reverse direction plus factor multiplication proves the
reduced common-root-branch reverse direction. -/
theorem theorem21RootCountBranchesReducedToCompatible_of_noCommonReverse
    (hreverse : theorem21RootCountBranchesToCompatibleNoCommonStatement) :
    theorem21RootCountBranchesReducedToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  rcases hbranches with hbranches | hcommon
  · exact hreverse hf hg hsgn hbranches.1 hbranches.2
  · exact CommonRootDeletionCompatibleBranch.compatible hcommon

/-- Reassemble the reduced common-root Liu target from separately proved
reduced forward and reverse directions. -/
theorem theorem21CompatibleRootCountReduced_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesReducedStatement)
    (hreverse : theorem21RootCountBranchesReducedToCompatibleStatement) :
    theorem21CompatibleRootCountReducedStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Reassemble the reduced common-root Liu target from the no-common forward
and no-common reverse directions. -/
theorem theorem21CompatibleRootCountReduced_of_noCommon_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleNoCommonStatement) :
    theorem21CompatibleRootCountReducedStatement :=
  theorem21CompatibleRootCountReduced_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesReduced_of_noCommonForward
      hforward)
    (theorem21RootCountBranchesReducedToCompatible_of_noCommonReverse
      hreverse)

/-- Projection form of the corrected full forward target. -/
theorem theorem21RootCountBranchesWithCommon_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesWithCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranchesWithCommon f g :=
  hforward hf hg hsgn hcompat

/-- The corrected full forward direction follows from the no-common forward
direction and the automatic common-root deletion branch. -/
theorem theorem21CompatibleToRootCountBranchesWithCommon_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesWithCommonStatement := by
  exact theorem21CompatibleToRootCountBranchesWithCommon_of_reduced
    (theorem21CompatibleToRootCountBranchesReduced_of_noCommonForward hforward)

/-- Branch-only reverse direction plus factor multiplication proves the
corrected common-root-branch reverse direction. -/
theorem theorem21RootCountBranchesWithCommonToCompatible_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21RootCountBranchesWithCommonToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  rcases hbranches with hbranches | hcommon
  · exact hreverse hf hg hsgn hbranches
  · exact CommonRootDeletionCompatibleBranch.compatible hcommon

/-- Reassemble the corrected common-root-branch Liu target from the
no-common-root forward direction and the branch-only reverse direction. -/
theorem theorem21CompatibleRootCountWithCommon_of_noCommonForward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21CompatibleRootCountWithCommonStatement := by
  intro f g hf hg hsgn
  constructor
  · exact
      theorem21CompatibleToRootCountBranchesWithCommon_of_noCommonForward
        hforward hf hg hsgn
  · exact
      theorem21RootCountBranchesWithCommonToCompatible_of_reverse
        hreverse hf hg hsgn

/-- Projection form of the isolated reverse direction of Liu Theorem 2.1. -/
theorem compatible_of_theorem21RootCountBranches_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  hreverse hf hg hsgn hbranches

/-- Projection form of the isolated nonconstant reverse direction of
Liu Theorem 2.1. -/
theorem compatible_of_theorem21RootCountBranches_of_reverse_nonconstant
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  hreverse hf hg hsgn hf_deg hg_deg hbranches

/-- Reverse direction of Liu Theorem 2.1 as a reusable projection. -/
theorem compatible_of_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_of_reverse
    (theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount h)
    hf hg hsgn hbranches

/-- Reverse direction of the nonconstant Liu Theorem 2.1 statement. -/
theorem compatible_of_theorem21RootCountBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_of_reverse_nonconstant
    (theorem21RootCountBranchesToCompatibleNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hbranches

/-- Isolated forward direction with the branch predicate swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_of_compatible_of_forward hforward
    hg hf hsgn.symm hcompat.comm

/-- Forward direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_symm_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- Isolated reverse direction with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  (compatible_of_theorem21RootCountBranches_of_reverse hreverse
    hg hf hsgn.symm hbranches).comm

/-- Isolated nonconstant reverse direction with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm_of_reverse_nonconstant
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  (compatible_of_theorem21RootCountBranches_of_reverse_nonconstant
    hreverse hg hf hsgn.symm hg_deg hf_deg hbranches).comm

/-- Reverse direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_symm_of_reverse
    (theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount h)
    hf hg hsgn hbranches

/-- Reverse direction of the nonconstant statement with the branch predicate
swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_symm_of_reverse_nonconstant
    (theorem21RootCountBranchesToCompatibleNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hbranches

/-- Projection form of Liu Theorem 2.1 after swapping the two polynomials. -/
theorem compatible_iff_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches g f :=
  ⟨theorem21RootCountBranches_symm_of_compatible h hf hg hsgn,
    compatible_of_theorem21RootCountBranches_symm h hf hg hsgn⟩

end LiuOppositeSigns
end RealRooted
