import RealRooted.LiuOppositeSigns.FactorReturnStatements
import RealRooted.LiuOppositeSigns.XSub.LeftSucc
import RealRooted.LiuOppositeSigns.XSub.SplittingTools
import RealRooted.LiuOppositeSigns.XSub.CubicQuadratic
import RealRooted.LiuOppositeSigns.XSub.QuarticCubic
import RealRooted.LiuOppositeSigns.XSub.QuarticCubicCommonRoot
import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary
import RealRooted.LiuOppositeSigns.XSub.LeftSuccDegreeTwo
import RealRooted.LiuOppositeSigns.XSub.LeftSuccDegreeThree
import RealRooted.MaWang
import RealRooted.SameDegreeCountFromAnalytic

/-!
# Liu opposite-sign compatibility theorem

This module contains the low-degree and analytic proof machinery for the
Liu opposite-sign compatibility theorem.  The theorem statement and
projection interface live in
`RealRooted.LiuOppositeSigns.Theorem21Statements`.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- In the nonconstant degree-one endpoint case, Liu's largest-root deletion
branch condition is automatic: deleting one endpoint leaves a degree-zero
polynomial, while the other endpoint has at most one root above any threshold.
-/
theorem theorem21RootCountBranches_of_natDegree_le_one_nonconstant
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hf_le : f.natDegree ≤ 1) (hg_le : g.natDegree ≤ 1) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn hf_deg hg_deg
  have hf_eq : f.natDegree = 1 :=
    le_antisymm hf_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hf_deg))
  have hg_eq : g.natDegree = 1 :=
    le_antisymm hg_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hg_deg))
  by_cases hs_le_r : s ≤ r
  · refine theorem21RootCountBranches_of_left
      ⟨hr, hs, hs_le_r, ?_⟩
    have hdelete_splits : (deleteRootFactor f r).Splits :=
      hr.deleteRootFactor_splits hf
    have hdelete_deg : (deleteRootFactor f r).natDegree = 0 := by
      rw [natDegree_deleteRootFactor, hf_eq]
    exact RootCountCompatible.of_left_natDegree_zero_right_natDegree_le_one
      hdelete_splits hg hdelete_deg hg_le
  · refine theorem21RootCountBranches_of_right
      ⟨hr, hs, lt_of_not_ge hs_le_r, ?_⟩
    have hdelete_splits : (deleteRootFactor g s).Splits :=
      hs.deleteRootFactor_splits hg
    have hdelete_deg : (deleteRootFactor g s).natDegree = 0 := by
      rw [natDegree_deleteRootFactor, hg_eq]
    exact (RootCountCompatible.of_left_natDegree_zero_right_natDegree_le_one
      hdelete_splits hf hdelete_deg hf_le).symm

/-- Degree `(2, 1)` forward subcase when the largest root lies on the
degree-two side, so deleting that root leaves two linear-or-constant endpoints.
-/
theorem theorem21RootCountBranches_of_left_largest_natDegree_le_two_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hs_le_r : s ≤ r) (hf_le : f.natDegree ≤ 2)
    (hg_le : g.natDegree ≤ 1) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_left
    (LeftRootCountBranch.of_largestRoots_natDegree_le_two_right_le_one
      hf hg hr hs hs_le_r hf_le hg_le)

/-- Degree `(1, 2)` forward subcase when the largest root lies on the
degree-two side, so deleting that root leaves two linear-or-constant endpoints.
-/
theorem theorem21RootCountBranches_of_right_largest_natDegree_le_one_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s)
    (hr_lt_s : r < s) (hf_le : f.natDegree ≤ 1)
    (hg_le : g.natDegree ≤ 2) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_right
    (RightRootCountBranch.of_largestRoots_left_le_one_right_le_two
      hf hg hr hs hr_lt_s hf_le hg_le)

/-- Explicit degree `(3, 2)` root-data forward subcase when the largest root
lies on the cubic side and the deletion pair has overlapping root intervals.
-/
theorem theorem21RootCountBranches_of_left_largest_roots_triple_pair
    {f g : ℝ[X]} {r s a b c d : ℝ}
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hs_le_r : s ≤ r)
    (had : a ≤ d) (hcb : c ≤ b)
    (hfroots : f.roots = {a, b, r})
    (hffac : f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C r)))
    (hgroots : g.roots = {c, d}) (hf_ne : f ≠ 0) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_left
    (LeftRootCountBranch.of_roots_triple_pair_right
      hr hs hs_le_r had hcb hfroots hffac hgroots hf_ne)

/-- Explicit degree `(2, 3)` root-data forward subcase when the largest root
lies on the cubic side and the deletion pair has overlapping root intervals.
-/
theorem theorem21RootCountBranches_of_right_largest_roots_pair_triple
    {f g : ℝ[X]} {r s a b c d : ℝ}
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hr_lt_s : r < s)
    (had : a ≤ d) (hcb : c ≤ b)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d, s})
    (hgfac : g = C g.leadingCoeff * ((X - C c) * (X - C d) * (X - C s)))
    (hg_ne : g ≠ 0) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_right
    (RightRootCountBranch.of_roots_pair_triple_right
      hr hs hr_lt_s had hcb hfroots hgroots hgfac hg_ne)

/-- Low-degree endpoint forward direction for the nonconstant degree-one case.
The compatibility hypothesis is retained to match the Liu Theorem 2.1 forward
shape, although the root-count branch condition follows from degree alone. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_le_one_nonconstant
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hf_le : f.natDegree ≤ 1) (hg_le : g.natDegree ≤ 1)
    (_hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_natDegree_le_one_nonconstant
    hf hg hsgn hf_deg hg_deg hf_le hg_le

/-- The isolated forward direction of Liu Theorem 2.1 gives the pointwise
root-count gap bound. -/
theorem rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 :=
  rootCountAtOrAbove_abs_sub_le_two_of_theorem21RootCountBranches hsgn
    (hforward hf hg hsgn hcompat)

/-- The isolated nonconstant forward direction of Liu Theorem 2.1 gives the
pointwise root-count gap bound. -/
theorem
    rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 :=
  rootCountAtOrAbove_abs_sub_le_two_of_theorem21RootCountBranches hsgn
    (hforward hf hg hsgn hf_deg hg_deg hcompat)

theorem
    rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 :=
  rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

theorem
    rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 :=
  rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The isolated forward direction of Liu Theorem 2.1 gives the oriented
branch-wise pointwise root-count bounds. -/
theorem rootCountAtOrAbove_branch_bounds_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) :=
  rootCountAtOrAbove_branch_bounds_of_theorem21RootCountBranches hsgn
    (hforward hf hg hsgn hcompat)

/-- The isolated nonconstant forward direction of Liu Theorem 2.1 gives the
oriented branch-wise pointwise root-count bounds. -/
theorem rootCountAtOrAbove_branch_bounds_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) :=
  rootCountAtOrAbove_branch_bounds_of_theorem21RootCountBranches hsgn
    (hforward hf hg hsgn hf_deg hg_deg hcompat)

theorem
    rootCountAtOrAbove_branch_bounds_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) :=
  rootCountAtOrAbove_branch_bounds_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

theorem
    rootCountAtOrAbove_branch_bounds_of_compatible_of_theorem21CompatibleRootCount_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) :=
  rootCountAtOrAbove_branch_bounds_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The isolated forward direction of Liu Theorem 2.1 gives the normalized
positive-deletion count branches. -/
theorem theorem21PositiveDeletionCountBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21PositiveDeletionCountBranches f g :=
  theorem21PositiveDeletionCountBranches_of_theorem21RootCountBranches hf hg hsgn
    (hforward hf hg hsgn hcompat)

/-- The isolated nonconstant forward direction of Liu Theorem 2.1 gives the
normalized positive-deletion count branches. -/
theorem theorem21PositiveDeletionCountBranches_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCountBranches f g :=
  theorem21PositiveDeletionCountBranches_of_theorem21RootCountBranches hf hg hsgn
    (hforward hf hg hsgn hf_deg hg_deg hcompat)

theorem theorem21PositiveDeletionCountBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCountBranches f g :=
  theorem21PositiveDeletionCountBranches_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

theorem theorem21PositiveDeletionCountBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCountBranches f g :=
  theorem21PositiveDeletionCountBranches_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Positive-split x-subtraction target for an arbitrary endpoint degree
relation.  This is the common statement shape behind the same-, right-successor,
and left-successor translated half-pencil leaves. -/
def positiveSplitTranslatedXSubRightFamilyRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄ (r : ℝ),
    PositiveSplitRootCountPair f g →
    HasNonnegCoeffs (f.comp (X + C r)) →
    HasNonnegCoeffs (g.comp (X + C r)) →
    R f.natDegree g.natDegree →
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted positive-split x-subtraction target for an arbitrary
endpoint degree relation.  The predicate records endpoint restrictions on
`g.natDegree`. -/
def positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄ (r : ℝ),
    PositiveSplitRootCountPair f g →
    HasNonnegCoeffs (f.comp (X + C r)) →
    HasNonnegCoeffs (g.comp (X + C r)) →
    R f.natDegree g.natDegree →
    P g.natDegree →
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted relation x-subtraction targets transport along
endpoint predicate implications. -/
theorem positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R Q) :
    positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R P := by
  intro f g r hpair hfnn hgnn hdeg hgdeg μ hμ
  exact hQ r hpair hfnn hgnn hdeg (hPQ _ hgdeg) μ hμ

/-- The unrestricted relation x-subtraction target is the `P := True` case of
the predicate-restricted target. -/
theorem positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
    {R : ℕ → ℕ → Prop}
    (hsub : positiveSplitTranslatedXSubRightFamilyRelationStatement R) :
    positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R
      (fun _ => True) := by
  intro f g r hpair hfnn hgnn hdeg _ μ hμ
  exact hsub r hpair hfnn hgnn hdeg μ hμ

/-- A `P := True` relation x-subtraction target gives the unrestricted
relation target. -/
theorem positiveSplitTranslatedXSubRightFamilyRelation_of_predicate_true
    {R : ℕ → ℕ → Prop}
    (hsub :
      positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R
        (fun _ => True)) :
    positiveSplitTranslatedXSubRightFamilyRelationStatement R := by
  intro f g r hpair hfnn hgnn hdeg μ hμ
  exact hsub r hpair hfnn hgnn hdeg trivial μ hμ

/-- Same-degree positive-split subtraction-family target. -/
def positiveSplitSameDegreeTranslatedXSubRightFamilyStatement : Prop :=
  positiveSplitTranslatedXSubRightFamilyRelationStatement
    (fun m n => m = n)

/-- Predicate-restricted same-degree positive-split subtraction-family target. -/
def positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement
    (fun m n => m = n) P

/-- Right-successor positive-split subtraction-family target. -/
def positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement : Prop :=
  positiveSplitTranslatedXSubRightFamilyRelationStatement
    (fun m n => n = m + 1)

/-- Predicate-restricted right-successor positive-split subtraction-family
target. -/
def positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement
    (fun m n => n = m + 1) P

/-- Degree guardrail for the translated x-subtraction endpoint: in the
left-successor case, `g.comp (X + C r)` and `X * f.comp (X + C r)` differ by
two degrees, so this endpoint cannot be proved by a direct `Prec` witness. -/
theorem not_positiveSplitLeftSuccDegreeTranslatedXPrec
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hdeg : f.natDegree = g.natDegree + 1) :
    ¬ Prec (g.comp (X + C r)) (X * f.comp (X + C r)) := by
  intro hprec
  have hF_ne : f.comp (X + C r) ≠ 0 :=
    (hpair.left_pos.comp_X_add_C r).ne_zero
  have hXF_deg :
      (X * f.comp (X + C r)).natDegree =
        (f.comp (X + C r)).natDegree + 1 :=
    natDegree_X_mul hF_ne
  have hF_deg : (f.comp (X + C r)).natDegree = f.natDegree := by
    simp [Polynomial.natDegree_comp]
  have hG_deg : (g.comp (X + C r)).natDegree = g.natDegree := by
    simp [Polynomial.natDegree_comp]
  have hgap :
      (g.comp (X + C r)).natDegree + 1 <
        (X * f.comp (X + C r)).natDegree := by
    rw [hXF_deg, hF_deg, hG_deg]
    lia
  exact not_prec_of_left_natDegree_succ_lt_right hgap hprec

/-- Quadratic terminal case for the x-subtraction pencil with two degree-one
endpoints and a nonnegative constant term on the right endpoint. -/
lemma splits_X_mul_sub_C_mul_of_natDegree_one_one_right_nonneg
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 1)
    (hqnn : HasNonnegCoeffs q) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let a := p.coeff 1
  let b := p.coeff 0
  let c := q.coeff 1
  let d := q.coeff 0
  have hp_eq : p = C a * X + C b := by
    simpa [a, b] using Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le
  have hq_eq : q = C c * X + C d := by
    simpa [c, d] using Polynomial.eq_X_add_C_of_natDegree_le_one hqdeg.le
  have ha_pos : 0 < a := by
    simpa [HasPosLeadingCoeff, hpdeg, leadingCoeff, a] using hp_pos
  have hd_nonneg : 0 ≤ d := by
    simpa [d] using hqnn 0
  have hpoly :
      X * p - C μ * q =
        C a * X ^ 2 + C (b - μ * c) * X + C (-μ * d) := by
    rw [hp_eq, hq_eq]
    simp [C_mul, C_sub, C_neg]
    ring
  have hprod_nonneg : 0 ≤ 4 * a * μ * d := by positivity
  have hdisc : 0 ≤ discrim a (b - μ * c) (-μ * d) := by
    rw [discrim]
    nlinarith [sq_nonneg (b - μ * c), hprod_nonneg]
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg ha_pos.ne' hdisc

/-- Linear-or-constant terminal case for the x-subtraction pencil. -/
lemma splits_X_mul_sub_C_mul_of_left_natDegree_zero_right_natDegree_le_one
    {p q : ℝ[X]} (hpdeg : p.natDegree = 0) (hqdeg : q.natDegree ≤ 1)
    (μ : ℝ) :
    (X * p - C μ * q).Splits := by
  apply Polynomial.Splits.of_natDegree_le_one
  have hleft : (X * p).natDegree ≤ 1 := by
    calc
      (X * p).natDegree ≤ X.natDegree + p.natDegree :=
        Polynomial.natDegree_mul_le
      _ = 1 := by simp [hpdeg]
  have hright : (C μ * q).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le μ q).trans hqdeg
  simpa using Polynomial.natDegree_sub_le_of_le hleft hright

/-- Degree-zero right endpoint base case for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
    {f g : ℝ[X]} {r : ℝ}
    (_hpair : PositiveSplitRootCountPair f g)
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (_hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ _hμ
  have hfdeg : f.natDegree = 0 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 0 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree ≤ 1 := by
    have hGdeg_eq : (g.comp (X + C r)).natDegree = 0 := by
      simpa [Polynomial.natDegree_comp] using hgdeg
    exact hGdeg_eq.le.trans (by norm_num)
  exact splits_X_mul_sub_C_mul_of_left_natDegree_zero_right_natDegree_le_one
    hFdeg hGdeg μ

/-- Degree-one right endpoint case for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 1 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_natDegree_one_one_right_nonneg
    (hpair.left_pos.comp_X_add_C r) hFdeg hGdeg hgnn hμ

/-- Low-degree right endpoint cases for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hzero : g.natDegree = 0
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
      hpair hfnn hgnn hdeg hzero
  · have hone : g.natDegree = 1 := by
      lia
    exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_one
      hpair hfnn hgnn hdeg hone

/-- Degree-one right endpoint base case for the right-successor
sign-normalized x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r : ℝ}
    (_hpair : PositiveSplitRootCountPair f g)
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (_hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ _hμ
  have hfdeg : f.natDegree = 0 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 0 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree ≤ 1 := by
    simpa [Polynomial.natDegree_comp] using hgdeg.le
  exact splits_X_mul_sub_C_mul_of_left_natDegree_zero_right_natDegree_le_one
    hFdeg hGdeg μ

/-- Pack the degree-zero right endpoint terminal as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 0) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-one right endpoint terminal as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 1) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the low-degree right endpoint terminals as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 1) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-one right endpoint terminal as a predicate-restricted
right-successor sign-normalized x-subtraction target. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 1) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    hpair hfnn hgnn hdeg hgdeg

/-- In the `(1, 2)` positive split root-count case, the lower quadratic root
cannot lie strictly above the linear root. -/
lemma lower_quadratic_root_le_singleton_root_of_positiveSplitRootCountPair_one_two
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c : ℝ} (hab : a ≤ b) (hfroots : f.roots = {c})
    (hgroots : g.roots = {a, b}) :
    a ≤ c := by
  by_contra hac
  have hca : c < a := lt_of_not_ge hac
  let x : ℝ := (a + c) / 2
  have hcx : c < x := by
    dsimp [x]
    linarith
  have hxa : x ≤ a := by
    dsimp [x]
    linarith
  have hxb : x ≤ b := hxa.trans hab
  have hcount := h.count.right_sub_le_one x
  have hf_count : rootCountAtOrAbove f x = 0 := by
    rw [rootCountAtOrAbove, hfroots]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r),
      if_neg (not_le.mpr hcx)]
    simp
  have hg_count : rootCountAtOrAbove g x = 2 := by
    rw [rootCountAtOrAbove, hgroots]
    simp only [Multiset.insert_eq_cons]
    rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxb]
    simp
  rw [hf_count, hg_count] at hcount
  norm_num at hcount

/-- In the `(2, 2)` positive split root-count case, the two ordered root
intervals overlap. -/
lemma roots_overlap_of_positiveSplitRootCountPair_two_two
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d}) :
    a ≤ d ∧ c ≤ b := by
  constructor
  · by_contra had
    have hda : d < a := lt_of_not_ge had
    let x : ℝ := (a + d) / 2
    have hdx : d < x := by
      dsimp [x]
      linarith
    have hxa : x ≤ a := by
      dsimp [x]
      linarith
    have hxb : x ≤ b := hxa.trans hab
    have hcx : c < x := lt_of_le_of_lt hcd hdx
    have hcount := h.count.left_sub_le_one x
    have hf_count : rootCountAtOrAbove f x = 2 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa]
      rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxb]
      simp
    have hg_count : rootCountAtOrAbove g x = 0 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xc : ¬ x ≤ c := not_le.mpr hcx
      have hnot_xd : ¬ x ≤ d := not_le.mpr hdx
      simp [hnot_xc, hnot_xd]
    rw [hf_count, hg_count] at hcount
    norm_num at hcount
  · by_contra hcb
    have hbc : b < c := lt_of_not_ge hcb
    let x : ℝ := (b + c) / 2
    have hbx : b < x := by
      dsimp [x]
      linarith
    have hxc : x ≤ c := by
      dsimp [x]
      linarith
    have hxd : x ≤ d := hxc.trans hcd
    have hax : a < x := lt_of_le_of_lt hab hbx
    have hcount := h.count.right_sub_le_one x
    have hf_count : rootCountAtOrAbove f x = 0 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      simp [hnot_xa, hnot_xb]
    have hg_count : rootCountAtOrAbove g x = 2 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.filter_cons_of_pos ({d} : Multiset ℝ) hxc]
      rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxd]
      simp
    rw [hf_count, hg_count] at hcount
    norm_num at hcount

/-- Discriminant certificate for the degree-one/degree-two x-subtraction
leaf.  The normalized hypotheses say that the quadratic roots `a ≤ b` and
linear root `c` are nonpositive after translation, and that the linear root is
not below the lower quadratic root. -/
def xSubLinearQuadraticDiscrimNonnegStatement : Prop :=
  ∀ {a b c μ : ℝ},
    a ≤ b → a ≤ c → b ≤ 0 → c ≤ 0 → 0 < μ →
      0 ≤ discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b))

/-- Explicit discriminant certificate for the normalized case
`a ≤ c ≤ b ≤ 0`. -/
lemma xSubLinearQuadraticDiscrimNonneg_between
    {u v w μ : ℝ} (hu : 0 ≤ u) (_hv : 0 ≤ v) (hw : 0 ≤ w)
    (hμ : 0 < μ) :
    0 ≤ discrim (1 - μ) (v + w - μ * (u + v + 2 * w))
      (-μ * ((u + v + w) * w)) := by
  have hdisc :
      discrim (1 - μ) (v + w - μ * (u + v + 2 * w))
          (-μ * ((u + v + w) * w)) =
        (μ * (u + v) - (v + w)) ^ 2 + 4 * μ * u * w := by
    unfold discrim
    ring_nf
  rw [hdisc]
  positivity

/-- Explicit discriminant certificate for the normalized case
`a ≤ b ≤ c ≤ 0`. -/
lemma xSubLinearQuadraticDiscrimNonneg_right
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hμ : 0 < μ) :
    0 ≤ discrim (1 - μ) (w - μ * (u + 2 * v + 2 * w))
      (-μ * ((u + v + w) * (v + w))) := by
  have hdisc :
      discrim (1 - μ) (w - μ * (u + 2 * v + 2 * w))
          (-μ * ((u + v + w) * (v + w))) =
        (μ * u + w) ^ 2 + 4 * μ * v * (u + v + w) := by
    unfold discrim
    ring_nf
  rw [hdisc]
  positivity

/-- The discriminant certificate needed in the degree-one/degree-two
x-subtraction leaf. -/
theorem xSubLinearQuadraticDiscrimNonneg :
    xSubLinearQuadraticDiscrimNonnegStatement := by
  intro a b c μ hab hac hb0 hc0 hμ
  by_cases hcb : c ≤ b
  · let u : ℝ := c - a
    let v : ℝ := b - c
    let w : ℝ := -b
    have hu : 0 ≤ u := by
      dsimp [u]
      linarith
    have hv : 0 ≤ v := by
      dsimp [v]
      linarith
    have hw : 0 ≤ w := by
      dsimp [w]
      linarith
    have hdisc :
        discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) =
          discrim (1 - μ) (v + w - μ * (u + v + 2 * w))
            (-μ * ((u + v + w) * w)) := by
      dsimp [u, v, w]
      unfold discrim
      ring_nf
    rw [hdisc]
    exact xSubLinearQuadraticDiscrimNonneg_between hu hv hw hμ
  · have hbc : b ≤ c := le_of_not_ge hcb
    let u : ℝ := b - a
    let v : ℝ := c - b
    let w : ℝ := -c
    have hu : 0 ≤ u := by
      dsimp [u]
      linarith
    have hv : 0 ≤ v := by
      dsimp [v]
      linarith
    have hw : 0 ≤ w := by
      dsimp [w]
      linarith
    have hdisc :
        discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) =
          discrim (1 - μ) (w - μ * (u + 2 * v + 2 * w))
            (-μ * ((u + v + w) * (v + w))) := by
      dsimp [u, v, w]
      unfold discrim
      ring_nf
    rw [hdisc]
    exact xSubLinearQuadraticDiscrimNonneg_right hu hv hw hμ

/-- Normalized monic arithmetic leaf for the degree-one/degree-two
x-subtraction endpoint. -/
def xSubLinearQuadraticSplitsStatement : Prop :=
  ∀ {a b c μ : ℝ},
    a ≤ b → a ≤ c → b ≤ 0 → c ≤ 0 → 0 < μ →
      (X * (X - C c) - C μ * ((X - C a) * (X - C b))).Splits

/-- The normalized discriminant certificate implies the monic
linear/quadratic x-subtraction leaf. -/
theorem xSubLinearQuadraticSplits_of_discrim
    (harith : xSubLinearQuadraticDiscrimNonnegStatement) :
    xSubLinearQuadraticSplitsStatement := by
  intro a b c μ hab hac hb0 hc0 hμ
  have hpoly :
      X * (X - C c) - C μ * ((X - C a) * (X - C b)) =
        C (1 - μ) * X ^ 2 + C (-c + μ * (a + b)) * X +
          C (-μ * (a * b)) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1]
    ring_nf
  have hdisc : 0 ≤ discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) :=
    harith hab hac hb0 hc0 hμ
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg_or_linear hdisc

/-- The normalized monic degree-one/degree-two x-subtraction leaf. -/
theorem xSubLinearQuadraticSplits : xSubLinearQuadraticSplitsStatement :=
  xSubLinearQuadraticSplits_of_discrim xSubLinearQuadraticDiscrimNonneg

/-- The normalized monic linear/quadratic x-subtraction leaf implies the
degree-one/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two_of_monic
    (hmono : xSubLinearQuadraticSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨c, hproots, hpfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hpair.left_splits hpdeg
  obtain ⟨a, b, hab, hqroots, hqfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.right_splits hqdeg
  have hac : a ≤ c :=
    lower_quadratic_root_le_singleton_root_of_positiveSplitRootCountPair_one_two
      hpair hab hproots hqroots
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn b hb_mem
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ p.roots := by
      rw [hproots]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn c hc_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] := X * (X - C c) - C ν * ((X - C a) * (X - C b))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hac hb0 hc0 hν_pos
  have hpfacA : p = C A * (X - C c) := by
    simpa [A] using hpfac
  have hqfacB : q = C B * ((X - C a) * (X - C b)) := by
    simpa [B] using hqfac
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfacA, hqfacB]
    dsimp [inner, ν]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hA_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-one/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two_of_monic
    xSubLinearQuadraticSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Normalized monic arithmetic leaf for the degree-two/degree-two
x-subtraction endpoint. -/
def xSubQuadraticQuadraticSplitsStatement : Prop :=
  ∀ {a b c d μ : ℝ},
    a ≤ b → c ≤ d → a ≤ d → c ≤ b → b ≤ 0 → d ≤ 0 → 0 < μ →
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))).Splits

/-- A monic quadratic minus a positive multiple of a linear factor splits
whenever the linear root lies weakly below the upper quadratic root. -/
lemma quadraticSubLinear_splits_of_right_root_le_upper
    {a b c μ : ℝ} (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits := by
  have hpoly :
      ((X - C a) * (X - C b)) - C μ * (X - C c) =
        C 1 * X ^ 2 + C (-(a + b + μ)) * X + C (a * b + μ * c) := by
    simp only [C_add, C_mul, C_neg, C_1]
    ring
  have hdisc : 0 ≤ discrim 1 (-(a + b + μ)) (a * b + μ * c) := by
    by_cases hac : a ≤ c
    · let u : ℝ := c - a
      let v : ℝ := b - c
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hdisc_eq :
          discrim 1 (-(a + b + μ)) (a * b + μ * c) =
            (μ + v - u) ^ 2 + 4 * u * v := by
        dsimp [u, v]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
    · have hca : c ≤ a := le_of_not_ge hac
      let u : ℝ := a - c
      let v : ℝ := b - a
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hdisc_eq :
          discrim 1 (-(a + b + μ)) (a * b + μ * c) =
            μ ^ 2 + 4 * μ * u + 2 * μ * v + v ^ 2 := by
        dsimp [u, v]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg one_ne_zero hdisc

/-- If the linear root lies strictly above the upper quadratic root, then some
positive subtraction coefficient makes the monic quadratic-minus-linear pencil
fail to split. -/
lemma exists_quadraticSubLinear_not_splits_of_upper_lt_right_root
    {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits := by
  let μ : ℝ := 2 * c - a - b
  have hμ : 0 < μ := by
    dsimp [μ]
    linarith
  refine ⟨μ, hμ, ?_⟩
  have hpoly :
      ((X - C a) * (X - C b)) - C μ * (X - C c) =
        C 1 * X ^ 2 + C (-(a + b + μ)) * X + C (a * b + μ * c) := by
    simp only [C_add, C_mul, C_neg, C_1]
    ring
  have hdisc : discrim 1 (-(a + b + μ)) (a * b + μ * c) < 0 := by
    have hac : a < c := lt_of_le_of_lt hab hbc
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos (sub_pos.mpr hac) (sub_pos.mpr hbc)
    have hdisc_eq :
        discrim 1 (-(a + b + μ)) (a * b + μ * c) =
          -4 * ((c - a) * (c - b)) := by
      dsimp [μ]
      unfold discrim
      ring_nf
    rw [hdisc_eq]
    nlinarith
  intro hsplit
  exact (quadraticPoly_not_splits_of_discrim_neg one_ne_zero hdisc) (by
    simpa [hpoly] using hsplit)

/-- The sign-normalized quadratic/linear endpoint is not compatible when the
linear root lies strictly above the upper quadratic root. -/
lemma not_compatible_quadratic_neg_linear_of_upper_lt_right_root
    {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) :
    ¬ Compatible ((X - C a) * (X - C b)) (-(X - C c)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubLinear_not_splits_of_upper_lt_right_root hab hbc
  intro hcompat
  have hcase := hcompat (1 : ℝ) μ zero_le_one (le_of_lt hμ)
  have hcombo_eq :
      C (1 : ℝ) * ((X - C a) * (X - C b)) + C μ * (-(X - C c)) =
        (X - C a) * (X - C b) - C μ * (X - C c) := by
    simp only [C_1, one_mul]
    ring_nf
  have hcase' :
      ((X - C a) * (X - C b) - C μ * (X - C c) = 0) ∨
        ((X - C a) * (X - C b) - C μ * (X - C c) ≠ 0 ∧
          ((X - C a) * (X - C b) - C μ * (X - C c)).Splits) := by
    rw [hcombo_eq] at hcase
    exact hcase
  rcases hcase' with hzero | ⟨_, hsplit⟩
  · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
  · exact hnot_splits hsplit

/-- The quadratic/linear factor endpoint is not compatible when the leading
coefficients have opposite signs and the linear root lies strictly above the
upper quadratic root. -/
lemma not_compatible_scaled_quadratic_linear_of_opposite_of_upper_lt_right_root
    {a b c A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b < c) :
    ¬ Compatible (C A * ((X - C a) * (X - C b))) (C B * (X - C c)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubLinear_not_splits_of_upper_lt_right_root hab hbc
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) * (C A * ((X - C a) * (X - C b))) +
            C (μ / B) * (C B * (X - C c)) =
          -(((X - C a) * (X - C b)) - C μ * (X - C c)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b)) - C μ * (X - C c) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) * (C A * ((X - C a) * (X - C b))) +
            C (μ / (-B)) * (C B * (X - C c)) =
          ((X - C a) * (X - C b)) - C μ * (X - C c) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- Normalized discriminant identity for the bad quadratic/quadratic nested
root order. -/
lemma discrim_quadraticSubQuadratic_inner_vertex {u v w : ℝ}
    (hv : v ≠ 0) :
    let μ := (u * v + 2 * u * w + v ^ 2 + v * w) / v ^ 2
    discrim (1 - μ) (-(0 + (u + v + w)) + μ * (u + (u + v)))
      (0 * (u + v + w) - μ * (u * (u + v))) =
        -4 * u * w * (u + v) * (v + w) / v ^ 2 := by
  intro μ
  dsimp [μ]
  have hv2_ne : v ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hv
  unfold discrim
  field_simp [hv2_ne]
  ring

/-- If the two roots of one monic quadratic lie strictly inside the root
interval of another, then some positive monic quadratic-minus-quadratic
pencil fails to split. -/
lemma exists_quadraticSubQuadratic_not_splits_of_inner_roots
    {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))).Splits := by
  by_cases hcd_eq : c = d
  · let μ : ℝ := ((b - a) ^ 2 + 1) / (4 * (c - a) * (b - c))
    subst d
    have hca_pos : 0 < c - a := sub_pos.mpr hac
    have hbc_pos : 0 < b - c := sub_pos.mpr (by linarith)
    have hden_pos : 0 < 4 * (c - a) * (b - c) := by positivity
    have hden_ne : 4 * (c - a) * (b - c) ≠ 0 := ne_of_gt hden_pos
    have hμ_pos : 0 < μ := by
      dsimp [μ]
      positivity
    have hμ_gt_one : 1 < μ := by
      dsimp [μ]
      have hnum_gt : 4 * (c - a) * (b - c) < (b - a) ^ 2 + 1 := by
        nlinarith [sq_nonneg ((c - a) - (b - c))]
      rw [one_lt_div hden_pos]
      linarith
    refine ⟨μ, hμ_pos, ?_⟩
    have hlead_ne : (1 - μ) ≠ 0 := by linarith
    have hdisc :
        discrim (1 - μ) (-(a + b) + μ * (c + c))
            (a * b - μ * (c * c)) < 0 := by
      have hdisc_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + c))
              (a * b - μ * (c * c)) =
            -1 := by
        dsimp [μ]
        unfold discrim
        field_simp [hden_ne]
        ring_nf
      rw [hdisc_eq]
      norm_num
    intro hsplit
    have hpoly :
        ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C c)) =
          C (1 - μ) * X ^ 2 + C (-(a + b) + μ * (c + c)) * X +
            C (a * b - μ * (c * c)) := by
      simp only [C_add, C_mul, C_neg, C_sub, C_1]
      ring
    exact
      (quadraticPoly_not_splits_of_discrim_neg hlead_ne hdisc)
        (by simpa [hpoly] using hsplit)
  · have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
    let u : ℝ := c - a
    let v : ℝ := d - c
    let w : ℝ := b - d
    let μ : ℝ := (u * v + 2 * u * w + v ^ 2 + v * w) / v ^ 2
    have hu : 0 < u := by
      dsimp [u]
      linarith
    have hv : 0 < v := by
      dsimp [v]
      linarith
    have hw : 0 < w := by
      dsimp [w]
      linarith
    have hμ_pos : 0 < μ := by
      dsimp [μ]
      positivity
    have hμ_gt_one : 1 < μ := by
      dsimp [μ]
      have hnum_gt : v ^ 2 < u * v + 2 * u * w + v ^ 2 + v * w := by
        nlinarith [mul_pos hu hv, mul_pos hu hw, mul_pos hv hw]
      rw [one_lt_div (by positivity : 0 < v ^ 2)]
      linarith
    refine ⟨μ, hμ_pos, ?_⟩
    have hlead_ne : (1 - μ) ≠ 0 := by linarith
    have hdisc :
        discrim (1 - μ) (-(a + b) + μ * (c + d))
            (a * b - μ * (c * d)) < 0 := by
      have hroots_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + d))
              (a * b - μ * (c * d)) =
            discrim (1 - μ)
              (-(0 + (u + v + w)) + μ * (u + (u + v)))
              (0 * (u + v + w) - μ * (u * (u + v))) := by
        dsimp [u, v, w]
        unfold discrim
        ring_nf
      rw [hroots_eq]
      rw [discrim_quadraticSubQuadratic_inner_vertex hv.ne']
      have hrewrite :
          -4 * u * w * (u + v) * (v + w) / v ^ 2 =
            -(4 * u * w * (u + v) * (v + w) / v ^ 2) := by
        ring
      rw [hrewrite]
      have hpos : 0 < 4 * u * w * (u + v) * (v + w) / v ^ 2 := by
        positivity
      linarith
    intro hsplit
    have hpoly :
        ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d)) =
          C (1 - μ) * X ^ 2 + C (-(a + b) + μ * (c + d)) * X +
            C (a * b - μ * (c * d)) := by
      simp only [C_add, C_mul, C_neg, C_sub, C_1]
      ring
    exact
      (quadraticPoly_not_splits_of_discrim_neg hlead_ne hdisc)
        (by simpa [hpoly] using hsplit)

/-- The scaled quadratic/quadratic endpoint is not compatible when one pair of
roots lies strictly inside the other and the leading coefficients have
opposite signs. -/
lemma not_compatible_scaled_quadratic_quadratic_of_opposite_of_inner_roots
    {a b c d A B : ℝ} (hAB : A * B < 0)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b)))
      (C B * ((X - C c) * (X - C d))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubQuadratic_not_splits_of_inner_roots hac hcd hdb
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) * (C A * ((X - C a) * (X - C b))) +
            C (μ / B) * (C B * ((X - C c) * (X - C d))) =
          -(((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b)) -
              C μ * ((X - C c) * (X - C d)) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) * (C A * ((X - C a) * (X - C b))) +
            C (μ / (-B)) * (C B * ((X - C c) * (X - C d))) =
          ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- In the degree `(2, 1)` endpoint, compatibility rules out the orientation
where the quadratic side has smaller largest root. -/
lemma not_compatible_of_natDegree_two_one_largest_lt
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 1)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hr_lt_s : r < s) :
    ¬ Compatible f g := by
  obtain ⟨a, b, hab, hfroots, hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hf hfdeg
  obtain ⟨c, hgroots, hgfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hg hgdeg
  have hb_le_r : b ≤ r := by
    have hb_mem : b ∈ f.roots := by
      rw [hfroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact hr.roots_le b hb_mem
  have hs_eq_c : s = c := by
    have hs_mem : s ∈ g.roots := hs.mem_roots hsgn.right_ne_zero
    rw [hgroots] at hs_mem
    simpa using hs_mem
  have hb_lt_c : b < c := by
    rw [← hs_eq_c]
    exact lt_of_le_of_lt hb_le_r hr_lt_s
  intro hcompat
  exact
    not_compatible_scaled_quadratic_linear_of_opposite_of_upper_lt_right_root
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hb_lt_c (by
        rw [hffac, hgfac] at hcompat
        exact hcompat)

/-- Forward degree `(2, 1)` endpoint case of Liu's root-count branch theorem.
Compatibility forces the largest root to lie on the quadratic side, and the
existing low-degree branch constructor then applies. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_two_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 1) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  by_cases hs_le_r : s ≤ r
  · exact theorem21RootCountBranches_of_left_largest_natDegree_le_two_one
      hf hg hr hs hs_le_r (by rw [hfdeg]) (by rw [hgdeg])
  · exact False.elim
      (not_compatible_of_natDegree_two_one_largest_lt
        hf hg hsgn hfdeg hgdeg hr hs (lt_of_not_ge hs_le_r) hcompat)

/-- In the degree `(1, 2)` endpoint, compatibility rules out the orientation
where the quadratic side has smaller largest root. -/
lemma not_compatible_of_natDegree_one_two_largest_gt
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 2)
    (hr : IsLargestRoot f r) (hs : IsLargestRoot g s) (hs_lt_r : s < r) :
    ¬ Compatible f g := by
  intro hcompat
  exact not_compatible_of_natDegree_two_one_largest_lt
    hg hf hsgn.symm hgdeg hfdeg hs hr hs_lt_r hcompat.comm

/-- Forward degree `(1, 2)` endpoint case with distinct largest roots.
Compatibility forces the largest root to lie on the quadratic side, and the
existing low-degree branch constructor then applies. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_one_two_of_largest_ne
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hfdeg : f.natDegree = 1)
    (hgdeg : g.natDegree = 2) (hr : IsLargestRoot f r)
    (hs : IsLargestRoot g s) (hrs_ne : r ≠ s) :
    theorem21RootCountBranches f g := by
  rcases lt_or_gt_of_ne hrs_ne with hr_lt_s | hs_lt_r
  · exact theorem21RootCountBranches_of_right_largest_natDegree_le_one_two
      hf hg hr hs hr_lt_s (by rw [hfdeg]) (by rw [hgdeg])
  · exact False.elim
      (not_compatible_of_natDegree_one_two_largest_gt
        hf hg hsgn hfdeg hgdeg hr hs hs_lt_r hcompat)

/-- Forward degree `(1, 2)` endpoint case in the no-common-root regime used by
Liu's proof reduction.  The no-common hypothesis rules out the otherwise
separate equal-largest-root corner. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_one_two_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 2)
    (hno : NoCommonRoots f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  have hrs_ne : r ≠ s := by
    intro hrs
    exact (hno r hr.isRoot) (by simpa [hrs] using hs.isRoot)
  exact theorem21RootCountBranches_of_compatible_natDegree_one_two_of_largest_ne
    hf hg hsgn hcompat hfdeg hgdeg hr hs hrs_ne

/-- Mixed endpoint degree-two no-common forward case.  This combines the
checked `(2, 1)` obstruction with its `(1, 2)` no-common counterpart. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_one_two_or_two_one_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hdeg :
      (f.natDegree = 2 ∧ g.natDegree = 1) ∨
        (f.natDegree = 1 ∧ g.natDegree = 2)) :
    theorem21RootCountBranches f g := by
  rcases hdeg with hdeg | hdeg
  · exact theorem21RootCountBranches_of_compatible_natDegree_two_one
      hf hg hsgn hcompat hdeg.1 hdeg.2
  · exact theorem21RootCountBranches_of_compatible_natDegree_one_two_of_no_common
      hf hg hsgn hcompat hdeg.1 hdeg.2 hno

/-- No-common quadratic/quadratic forward endpoint case.  If the largest root
of one side lies to the right, deleting it leaves a singleton/two-root
comparison.  The only way that count comparison could fail is the bad nested
root order, which contradicts compatibility by the discriminant obstruction
above. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_two_two_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 2)
    (hno : NoCommonRoots f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨a, b, hab, hfroots, hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hf hfdeg
  obtain ⟨c, d, hcd, hgroots, hgfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hg hgdeg
  have hr_eq_b : r = b :=
    IsLargestRoot.eq_right_of_roots_pair hsgn.left_ne_zero hr hab hfroots
  have hs_eq_d : s = d :=
    IsLargestRoot.eq_right_of_roots_pair hsgn.right_ne_zero hs hcd hgroots
  have hdelete_f_roots : (deleteRootFactor f r).roots = {a} := by
    rw [hr_eq_b]
    exact roots_deleteRootFactor_eq_singleton_of_roots_pair_right
      hsgn.left_ne_zero hfroots hffac
  have hdelete_g_roots : (deleteRootFactor g s).roots = {c} := by
    rw [hs_eq_d]
    exact roots_deleteRootFactor_eq_singleton_of_roots_pair_right
      hsgn.right_ne_zero hgroots hgfac
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b)))
        (C g.leadingCoeff * ((X - C c) * (X - C d))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  by_cases hs_le_r : s ≤ r
  · have hca : c ≤ a := by
      by_contra hnot
      have hac : a < c := lt_of_not_ge hnot
      have hd_le_b : d ≤ b := by
        simpa [hr_eq_b, hs_eq_d] using hs_le_r
      have hb_root : f.IsRoot b :=
        (Polynomial.mem_roots hsgn.left_ne_zero).mp (by
          rw [hfroots]
          simp only [Multiset.insert_eq_cons]
          simp)
      have hd_root : g.IsRoot d :=
        (Polynomial.mem_roots hsgn.right_ne_zero).mp (by
          rw [hgroots]
          simp only [Multiset.insert_eq_cons]
          simp)
      have hdb_ne : d ≠ b := by
        intro hdb_eq
        exact (hno b hb_root) (by simpa [hdb_eq] using hd_root)
      have hdb : d < b := lt_of_le_of_ne hd_le_b hdb_ne
      exact
        not_compatible_scaled_quadratic_quadratic_of_opposite_of_inner_roots
          (A := f.leadingCoeff) (B := g.leadingCoeff)
          hsgn hac hcd hdb hcompat_fac
    exact theorem21RootCountBranches_of_left
      ⟨hr, hs, hs_le_r,
        RootCountCompatible.of_roots_singleton_pair
          hca hdelete_f_roots hgroots⟩
  · have hr_lt_s : r < s := lt_of_not_ge hs_le_r
    have hac : a ≤ c := by
      by_contra hnot
      have hca : c < a := lt_of_not_ge hnot
      have hb_lt_d : b < d := by
        simpa [hr_eq_b, hs_eq_d] using hr_lt_s
      exact
        not_compatible_scaled_quadratic_quadratic_of_opposite_of_inner_roots
          (a := c) (b := d) (c := a) (d := b)
          (A := g.leadingCoeff) (B := f.leadingCoeff)
          hsgn.symm hca hab hb_lt_d hcompat_fac.comm
    exact theorem21RootCountBranches_of_right
      ⟨hr, hs, hr_lt_s,
        RootCountCompatible.of_roots_pair_singleton
          hac hfroots hdelete_g_roots⟩

/-- Nonconstant degree-`≤ 2` no-common forward case, excluding only the
remaining quadratic-quadratic corner. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_le_two_nonquadratic_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 2) (hgdeg_le : g.natDegree ≤ 2)
    (hnot_quad_quad : ¬ (f.natDegree = 2 ∧ g.natDegree = 2)) :
    theorem21RootCountBranches f g := by
  have hf_cases : f.natDegree = 1 ∨ f.natDegree = 2 := by
    have hfdeg_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hfdeg_ne
    interval_cases f.natDegree <;> simp_all
  have hg_cases : g.natDegree = 1 ∨ g.natDegree = 2 := by
    have hgdeg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hgdeg_ne
    interval_cases g.natDegree <;> simp_all
  rcases hf_cases with hfdeg | hfdeg <;> rcases hg_cases with hgdeg | hgdeg
  · exact theorem21RootCountBranches_of_compatible_natDegree_le_one_nonconstant
      hf hg hsgn hfdeg_ne hgdeg_ne (by rw [hfdeg]) (by rw [hgdeg]) hcompat
  · exact theorem21RootCountBranches_of_compatible_natDegree_one_two_of_no_common
      hf hg hsgn hcompat hfdeg hgdeg hno
  · exact theorem21RootCountBranches_of_compatible_natDegree_two_one
      hf hg hsgn hcompat hfdeg hgdeg
  · exact False.elim (hnot_quad_quad ⟨hfdeg, hgdeg⟩)

/-- Nonconstant degree-`≤ 2` no-common forward case. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_le_two_of_no_common
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 2) (hgdeg_le : g.natDegree ≤ 2) :
    theorem21RootCountBranches f g := by
  by_cases hquad_quad : f.natDegree = 2 ∧ g.natDegree = 2
  · exact theorem21RootCountBranches_of_compatible_natDegree_two_two_of_no_common
      hf hg hsgn hcompat hquad_quad.1 hquad_quad.2 hno
  · exact
      theorem21RootCountBranches_of_compatible_natDegree_le_two_nonquadratic_of_no_common
        hf hg hsgn hcompat hno hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hquad_quad

/-- The remaining mixed endpoint-degree-three obstruction in root-order form.
For a compatible opposite-sign cubic/quadratic pair, the quadratic roots must
meet the two-root interval left after deleting the cubic largest root, and the
quadratic largest root must not exceed the cubic largest root. -/
def CompatibleCubicPairRootOrderStatement : Prop :=
  ∀ {f g : ℝ[X]} {a b c u v : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g →
        f.natDegree = 3 → g.natDegree = 2 →
          a ≤ b → b ≤ c → u ≤ v →
            f.roots = {a, b, c} → g.roots = {u, v} →
              u ≤ b ∧ a ≤ v ∧ v ≤ c

/-- Conditional degree `(3, 2)` no-common forward endpoint case.  Once the
cubic/quadratic root-order obstruction is known, the explicit deletion-branch
constructor gives Liu's root-count branch. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_three_two_of_cubicPairRootOrder
    (horder : CompatibleCubicPairRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 2) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨a, b, c, hab, hbc, hfroots, hffac⟩ :=
    exists_roots_triple_of_splits_natDegree_three hf hfdeg
  obtain ⟨u, v, huv, hgroots, _hgfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hg hgdeg
  obtain ⟨hub, hav, hvc⟩ :=
    horder hf hg hsgn hcompat hfdeg hgdeg hab hbc huv hfroots hgroots
  have hr_eq_c : r = c :=
    IsLargestRoot.eq_right_of_roots_triple hsgn.left_ne_zero hr hab hbc
      hfroots
  have hs_eq_v : s = v :=
    IsLargestRoot.eq_right_of_roots_pair hsgn.right_ne_zero hs huv hgroots
  have hs_le_r : s ≤ r := by
    rw [hr_eq_c, hs_eq_v]
    exact hvc
  have hfroots_r : f.roots = {a, b, r} := by
    rw [hr_eq_c]
    exact hfroots
  have hffac_r :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C r)) := by
    rw [hr_eq_c]
    exact hffac
  exact theorem21RootCountBranches_of_left_largest_roots_triple_pair
    (r := r) (s := s) (a := a) (b := b) (c := u) (d := v)
    hr hs hs_le_r hav hub hfroots_r hffac_r hgroots hsgn.left_ne_zero

/-- Conditional degree `(2, 3)` no-common forward endpoint case, obtained by
applying the cubic/quadratic root-order obstruction after swapping the pair. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_two_three_of_cubicPairRootOrder
    (horder : CompatibleCubicPairRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 3) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨a, b, hab, hfroots, _hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hf hfdeg
  obtain ⟨c, d, e, hcd, hde, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three hg hgdeg
  obtain ⟨had, hcb, hbe⟩ :=
    horder (f := g) (g := f) (a := c) (b := d) (c := e)
      (u := a) (v := b)
      hg hf hsgn.symm hcompat.comm hgdeg hfdeg hcd hde hab hgroots
      hfroots
  have hr_eq_b : r = b :=
    IsLargestRoot.eq_right_of_roots_pair hsgn.left_ne_zero hr hab hfroots
  have hs_eq_e : s = e :=
    IsLargestRoot.eq_right_of_roots_triple hsgn.right_ne_zero hs hcd hde
      hgroots
  have hb_root : f.IsRoot b :=
    (Polynomial.mem_roots hsgn.left_ne_zero).mp (by
      rw [hfroots]
      simp only [Multiset.insert_eq_cons]
      simp)
  have he_root : g.IsRoot e :=
    (Polynomial.mem_roots hsgn.right_ne_zero).mp (by
      rw [hgroots]
      simp only [Multiset.insert_eq_cons]
      simp)
  have hbe_ne : b ≠ e := by
    intro hbe_eq
    exact (hno b hb_root) (by simpa [hbe_eq] using he_root)
  have hb_lt_e : b < e := lt_of_le_of_ne hbe hbe_ne
  have hr_lt_s : r < s := by
    rw [hr_eq_b, hs_eq_e]
    exact hb_lt_e
  have hgroots_s : g.roots = {c, d, s} := by
    rw [hs_eq_e]
    exact hgroots
  have hgfac_s :
      g = C g.leadingCoeff * ((X - C c) * (X - C d) * (X - C s)) := by
    rw [hs_eq_e]
    exact hgfac
  exact theorem21RootCountBranches_of_right_largest_roots_pair_triple
    (r := r) (s := s) (a := a) (b := b) (c := c) (d := d)
    hr hs hr_lt_s had hcb hfroots hgroots_s hgfac_s hsgn.right_ne_zero

/-- Conditional no-common mixed degree-three/two forward endpoint package. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_three_two_or_two_three_of_cubicPairRootOrder
    (horder : CompatibleCubicPairRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hdeg :
      (f.natDegree = 3 ∧ g.natDegree = 2) ∨
        (f.natDegree = 2 ∧ g.natDegree = 3)) :
    theorem21RootCountBranches f g := by
  rcases hdeg with hdeg | hdeg
  · exact
      theorem21RootCountBranches_of_compatible_natDegree_three_two_of_cubicPairRootOrder
        horder hf hg hsgn hcompat hdeg.1 hdeg.2
  · exact
      theorem21RootCountBranches_of_compatible_natDegree_two_three_of_cubicPairRootOrder
        horder hf hg hsgn hcompat hno hdeg.1 hdeg.2

/-- The remaining cubic/linear endpoint-degree-three obstruction in root-order
form.  For a compatible opposite-sign cubic/linear pair, the linear root must
lie weakly between the lower and largest cubic roots. -/
def CompatibleCubicLinearRootOrderStatement : Prop :=
  ∀ {f g : ℝ[X]} {a b c u : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g →
        f.natDegree = 3 → g.natDegree = 1 →
          a ≤ b → b ≤ c →
            f.roots = {a, b, c} → g.roots = {u} →
              a ≤ u ∧ u ≤ c

/-- Conditional degree `(3, 1)` no-common forward endpoint case.  Once the
cubic/linear root-order obstruction is known, deleting the cubic largest root
leaves a quadratic/linear root-count comparison. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_three_one_of_cubicLinearRootOrder
    (horder : CompatibleCubicLinearRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 1) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨a, b, c, hab, hbc, hfroots, hffac⟩ :=
    exists_roots_triple_of_splits_natDegree_three hf hfdeg
  obtain ⟨u, hgroots, _hgfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hg hgdeg
  obtain ⟨hau, huc⟩ :=
    horder hf hg hsgn hcompat hfdeg hgdeg hab hbc hfroots hgroots
  have hr_eq_c : r = c :=
    IsLargestRoot.eq_right_of_roots_triple hsgn.left_ne_zero hr hab hbc
      hfroots
  have hs_eq_u : s = u := by
    have hs_mem : s ∈ g.roots := hs.mem_roots hsgn.right_ne_zero
    rw [hgroots] at hs_mem
    simpa using hs_mem
  have hs_le_r : s ≤ r := by
    rw [hr_eq_c, hs_eq_u]
    exact huc
  have hdelete_roots : (deleteRootFactor f r).roots = {a, b} := by
    rw [hr_eq_c]
    exact roots_deleteRootFactor_eq_pair_of_roots_triple_right
      hsgn.left_ne_zero hfroots hffac
  exact theorem21RootCountBranches_of_left
    ⟨hr, hs, hs_le_r,
      RootCountCompatible.of_roots_pair_singleton
        hau hdelete_roots hgroots⟩

/-- Conditional degree `(1, 3)` no-common forward endpoint case, obtained by
applying the cubic/linear root-order obstruction after swapping the pair. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_one_three_of_cubicLinearRootOrder
    (horder : CompatibleCubicLinearRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 3) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ :=
    exists_largestRoots hf hg hsgn
      (by rw [hfdeg]; norm_num) (by rw [hgdeg]; norm_num)
  obtain ⟨u, hfroots, _hffac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hf hfdeg
  obtain ⟨a, b, c, hab, hbc, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three hg hgdeg
  obtain ⟨hau, huc⟩ :=
    horder (f := g) (g := f) (a := a) (b := b) (c := c)
      (u := u) hg hf hsgn.symm hcompat.comm hgdeg hfdeg hab hbc
      hgroots hfroots
  have hr_eq_u : r = u := by
    have hr_mem : r ∈ f.roots := hr.mem_roots hsgn.left_ne_zero
    rw [hfroots] at hr_mem
    simpa using hr_mem
  have hs_eq_c : s = c :=
    IsLargestRoot.eq_right_of_roots_triple hsgn.right_ne_zero hs hab hbc
      hgroots
  have hu_root : f.IsRoot u :=
    (Polynomial.mem_roots hsgn.left_ne_zero).mp (by
      rw [hfroots]
      simp)
  have hc_root : g.IsRoot c :=
    (Polynomial.mem_roots hsgn.right_ne_zero).mp (by
      rw [hgroots]
      simp only [Multiset.insert_eq_cons]
      simp)
  have huc_ne : u ≠ c := by
    intro huc_eq
    exact (hno u hu_root) (by simpa [huc_eq] using hc_root)
  have hu_lt_c : u < c := lt_of_le_of_ne huc huc_ne
  have hr_lt_s : r < s := by
    rw [hr_eq_u, hs_eq_c]
    exact hu_lt_c
  have hdelete_roots : (deleteRootFactor g s).roots = {a, b} := by
    rw [hs_eq_c]
    exact roots_deleteRootFactor_eq_pair_of_roots_triple_right
      hsgn.right_ne_zero hgroots hgfac
  exact theorem21RootCountBranches_of_right
    ⟨hr, hs, hr_lt_s,
      RootCountCompatible.of_roots_singleton_pair
        hau hfroots hdelete_roots⟩

/-- Conditional nonconstant no-common forward direction through endpoint
degree three, excluding the remaining cubic/cubic corner. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_le_three_excluding_three_three
    (hlinear : CompatibleCubicLinearRootOrderStatement)
    (hpair : CompatibleCubicPairRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3)
    (hnot_three_three : ¬ (f.natDegree = 3 ∧ g.natDegree = 3)) :
    theorem21RootCountBranches f g := by
  by_cases hf_le_two : f.natDegree ≤ 2
  · by_cases hg_le_two : g.natDegree ≤ 2
    · exact theorem21RootCountBranches_of_compatible_natDegree_le_two_of_no_common
        hf hg hsgn hcompat hno hfdeg_ne hgdeg_ne hf_le_two hg_le_two
    · have hg_three : g.natDegree = 3 := by lia
      have hf_cases : f.natDegree = 1 ∨ f.natDegree = 2 := by
        have hf_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hfdeg_ne
        interval_cases f.natDegree <;> simp_all
      rcases hf_cases with hf_one | hf_two
      · exact
          theorem21RootCountBranches_of_compatible_natDegree_one_three_of_cubicLinearRootOrder
            hlinear hf hg hsgn hcompat hno hf_one hg_three
      · exact
          theorem21RootCountBranches_of_compatible_natDegree_two_three_of_cubicPairRootOrder
            hpair hf hg hsgn hcompat hno hf_two hg_three
  · have hf_three : f.natDegree = 3 := by lia
    by_cases hg_le_two : g.natDegree ≤ 2
    · have hg_cases : g.natDegree = 1 ∨ g.natDegree = 2 := by
        have hg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hgdeg_ne
        interval_cases g.natDegree <;> simp_all
      rcases hg_cases with hg_one | hg_two
      · exact
          theorem21RootCountBranches_of_compatible_natDegree_three_one_of_cubicLinearRootOrder
            hlinear hf hg hsgn hcompat hf_three hg_one
      · exact
          theorem21RootCountBranches_of_compatible_natDegree_three_two_of_cubicPairRootOrder
            hpair hf hg hsgn hcompat hf_three hg_two
    · have hg_three : g.natDegree = 3 := by lia
      exact False.elim (hnot_three_three ⟨hf_three, hg_three⟩)

/-- A monic cubic minus a positive multiple of a monic quadratic is still a
genuine cubic. -/
lemma natDegree_cubicSubQuadratic (a b c u v μ : ℝ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).natDegree = 3 := by
  compute_degree <;> norm_num

/-- A monic cubic minus a positive multiple of a monic quadratic is nonzero. -/
lemma cubicSubQuadratic_ne_zero (a b c u v μ : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_cubicSubQuadratic a b c u v μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- Evaluation form of a monic cubic minus a positive multiple of a monic
quadratic. -/
lemma eval_cubicSubQuadratic (a b c u v μ x : ℝ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).eval x =
      (x - a) * (x - b) * (x - c) - μ * ((x - u) * (x - v)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- Coefficient expansion of a monic cubic minus a monic quadratic. -/
lemma cubicSubQuadratic_eq_cubic_expansion (a b c u v μ : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v)) =
      C 1 * X ^ 3 + C (-(a + b + c + μ)) * X ^ 2 +
        C (a * b + a * c + b * c + μ * (u + v)) * X +
          C (-(a * b * c) - μ * (u * v)) := by
  simp only [C_add, C_mul, C_neg, C_sub, C_1]
  ring

/-- The cubic discriminant is invariant under translating a cubic written in
coefficient form. -/
lemma cubicDiscr_cubic_comp_X_add_C (a3 a2 a1 a0 r : ℝ) :
    cubicDiscr
        ((C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).comp
          (X + C r)) =
      cubicDiscr (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0) := by
  have hpoly :
      (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).comp
          (X + C r) =
        C a3 * X ^ 3 + C (3 * a3 * r + a2) * X ^ 2 +
          C (3 * a3 * r ^ 2 + 2 * a2 * r + a1) * X +
            C (a3 * r ^ 3 + a2 * r ^ 2 + a1 * r + a0) := by
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [hpoly, cubicDiscr_of_coeffs, cubicDiscr_of_coeffs]
  ring

/-- The upper left root gives a nonpositive value for the cubic-minus-quadratic
pencil under the root-count inequalities. -/
lemma eval_cubicSubQuadratic_at_upper_nonpos {a b c u v μ : ℝ}
    (hbc : b ≤ c) (hub : u ≤ b) (hvc : v ≤ c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).eval c ≤ 0 := by
  rw [eval_cubicSubQuadratic]
  have hcu_nonneg : 0 ≤ c - u := sub_nonneg.mpr (hub.trans hbc)
  have hcv_nonneg : 0 ≤ c - v := sub_nonneg.mpr hvc
  have hG_nonneg : 0 ≤ (c - u) * (c - v) :=
    mul_nonneg hcu_nonneg hcv_nonneg
  nlinarith [mul_nonneg (le_of_lt hμ) hG_nonneg]

/-- A monic cubic minus a lower-degree quadratic has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_cubicSubQuadratic (a b c u v μ : ℝ) :
    HasPosLeadingCoeff
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) := by
  have hcubic_pos : HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c)) := by
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hcubic_deg : ((X - C a) * (X - C b) * (X - C c)).natDegree = 3 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v))).natDegree <
      ((X - C a) * (X - C b) * (X - C c)).natDegree := by
    rw [hcubic_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hcubic_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C u) * (X - C v))) <
      degree ((X - C a) * (X - C b) * (X - C c)) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hcubic_pos

/-- The monic cubic-minus-quadratic pencil tends to `+∞` at `+∞`. -/
lemma tendsto_eval_cubicSubQuadratic_atTop_atTop (a b c u v μ : ℝ) :
    Tendsto
      (fun x =>
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_cubicSubQuadratic a b c u v μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_cubicSubQuadratic a b c u v μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- Common-root boundary for a monic cubic-minus-quadratic pencil.  Factoring
out the shared linear term leaves the proved quadratic-minus-linear lemma. -/
lemma cubicSubQuadratic_splits_of_common_root {r a b c μ : ℝ}
    (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (((X - C r) * ((X - C a) * (X - C b))) -
      C μ * ((X - C r) * (X - C c))).Splits := by
  let Q : ℝ[X] := ((X - C a) * (X - C b)) - C μ * (X - C c)
  have hQ : Q.Splits := by
    dsimp [Q]
    exact quadraticSubLinear_splits_of_right_root_le_upper hab hcb hμ
  have hfactor :
      ((X - C r) * ((X - C a) * (X - C b))) -
        C μ * ((X - C r) * (X - C c)) = (X - C r) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hQ

/-- Strict order case `u < a < v < b ≤ c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_u_a_v_b
    {a b c u v μ : ℝ} (hua : u < a) (hav : a < v) (hvb : v < b)
    (hbc : b ≤ c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hub : u < b := lt_trans hua (lt_trans hav hvb)
  have huc : u < c := lt_of_lt_of_le hub hbc
  have hvc : v < c := lt_of_lt_of_le hvb hbc
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hG_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hvb (le_of_lt hav) hbc
      (mul_neg_of_neg_of_pos hP_u_neg hP_a_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_b_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- Strict order case `u < a ≤ b < v < c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_u_a_b_v
    {a b c u v μ : ℝ} (hua : u < a) (hab : a ≤ b) (hbv : b < v)
    (hvc : v < c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hav : a < v := lt_of_le_of_lt hab hbv
  have hub : u < b := lt_of_lt_of_le hua hab
  have huc : u < c := lt_trans hub (lt_trans hbv hvc)
  have hbc : b ≤ c := le_of_lt (lt_trans hbv hvc)
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hG_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    nlinarith
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hbv hab (le_of_lt hvc)
      (mul_neg_of_neg_of_pos hP_u_neg hP_a_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_v_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- Strict order case `a < u ≤ v < b ≤ c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_a_u_v_b
    {a b c u v μ : ℝ} (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hbc : b ≤ c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hub : u < b := lt_of_le_of_lt huv hvb
  have hav : a < v := lt_of_lt_of_le hau huv
  have huc : u < c := lt_of_lt_of_le hub hbc
  have hvc : v < c := lt_of_lt_of_le hvb hbc
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    nlinarith
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hG_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hau hvb huv hbc
      (mul_neg_of_neg_of_pos hP_a_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_b_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- Strict order case `a < u < b < v < c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_a_u_b_v
    {a b c u v μ : ℝ} (hau : a < u) (hub : u < b) (hbv : b < v)
    (hvc : v < c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hav : a < v := lt_trans hau (lt_trans hub hbv)
  have huc : u < c := lt_trans hub (lt_trans hbv hvc)
  have hbc : b ≤ c := le_of_lt (lt_trans hbv hvc)
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hG_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    nlinarith
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hau hbv (le_of_lt hub) (le_of_lt hvc)
      (mul_neg_of_neg_of_pos hP_a_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_v_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- A monic cubic minus a positive multiple of a monic quadratic splits under the
weak root-count inequalities produced by the cubic/cubic `w = 0` boundary. -/
lemma cubicSubQuadratic_splits_of_roots_le {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases hua_eq : u = a
  · subst u
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := a) (a := b) (b := c) (c := v) hbc hvc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hva_eq : v = a
  · subst v
    have huc : u ≤ c := hub.trans hbc
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := a) (a := b) (b := c) (c := u) hbc huc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hub_eq : u = b
  · subst u
    have hac : a ≤ c := hab.trans hbc
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := c) (c := v) hac hvc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hvb_eq : v = b
  · subst v
    have hac : a ≤ c := hab.trans hbc
    have huc : u ≤ c := hub.trans hbc
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := c) (c := u) hac huc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hvc_eq : v = c
  · subst v
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := c) (a := a) (b := b) (c := u) hab hub hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  have hav_lt : a < v := lt_of_le_of_ne hav (by intro h; exact hva_eq h.symm)
  by_cases hua : u < a
  · by_cases hvb : v < b
    · exact cubicSubQuadratic_splits_of_order_u_a_v_b
        hua hav_lt hvb hbc hμ
    · have hbv : b < v :=
        lt_of_le_of_ne (le_of_not_gt hvb) (by intro h; exact hvb_eq h.symm)
      have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
      exact cubicSubQuadratic_splits_of_order_u_a_b_v
        hua hab hbv hvc_lt hμ
  · have hau : a < u :=
      lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
    by_cases hvb : v < b
    · exact cubicSubQuadratic_splits_of_order_a_u_v_b
        hau huv hvb hbc hμ
    · have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
      have hbv : b < v :=
        lt_of_le_of_ne (le_of_not_gt hvb) (by intro h; exact hvb_eq h.symm)
      have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
      exact cubicSubQuadratic_splits_of_order_a_u_b_v
        hau hub_lt hbv hvc_lt hμ

/-- Boundary case of the quadratic/quadratic leaf when the right endpoint has
root zero.  Factoring out `X` leaves a quadratic-minus-linear pencil. -/
lemma xSubQuadraticQuadraticSplits_of_right_root_zero
    {a b c μ : ℝ} (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * X)).Splits := by
  have hquad : (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits :=
    quadraticSubLinear_splits_of_right_root_le_upper hab hcb hμ
  have hfactor :
      X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * X) =
          X * (((X - C a) * (X - C b)) - C μ * (X - C c)) := by
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hquad

/-- Boundary case of the quadratic/quadratic leaf when the two quadratic
endpoints share a root. -/
lemma xSubQuadraticQuadraticSplits_of_common_root
    {r s t μ : ℝ} (hs0 : s ≤ 0) (ht0 : t ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * (X - C s)) -
      C μ * ((X - C r) * (X - C t))).Splits := by
  have hquad₀ :
      (((X - C s) * (X - C 0)) - C μ * (X - C t)).Splits :=
    quadraticSubLinear_splits_of_right_root_le_upper
      (a := s) (b := 0) (c := t) hs0 ht0 hμ
  have hquad : (X * (X - C s) - C μ * (X - C t)).Splits := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hquad₀
  have hfactor :
      X * ((X - C r) * (X - C s)) -
        C μ * ((X - C r) * (X - C t)) =
          (X - C r) * (X * (X - C s) - C μ * (X - C t)) := by
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hquad

/-- The normalized quadratic/quadratic x-subtraction polynomial is a genuine
cubic. -/
lemma natDegree_xSubQuadraticQuadratic (a b c d μ : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).natDegree = 3 := by
  compute_degree <;> norm_num

/-- The normalized quadratic/quadratic x-subtraction polynomial is nonzero. -/
lemma xSubQuadraticQuadratic_ne_zero (a b c d μ : ℝ) :
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubQuadraticQuadratic a b c d μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized quadratic/quadratic x-subtraction polynomial has positive
leading coefficient. -/
lemma hasPosLeadingCoeff_xSubQuadraticQuadratic (a b c d μ : ℝ) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))) := by
  have hquad_pos : HasPosLeadingCoeff ((X - C a) * (X - C b)) :=
    (hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)
  have hleft_pos : HasPosLeadingCoeff (X * ((X - C a) * (X - C b))) :=
    hquad_pos.X_mul
  have hleft_deg : (X * ((X - C a) * (X - C b))).natDegree = 3 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C c) * (X - C d))).natDegree <
      (X * ((X - C a) * (X - C b))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C c) * (X - C d))) <
      degree (X * ((X - C a) * (X - C b))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized quadratic/quadratic x-subtraction leaf. -/
lemma eval_xSubQuadraticQuadratic (a b c d μ x : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).eval x =
      x * ((x - a) * (x - b)) - μ * ((x - c) * (x - d)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The normalized quadratic/quadratic x-subtraction polynomial tends to
`-∞` at `-∞`. -/
lemma tendsto_eval_xSubQuadraticQuadratic_atBot_atBot (a b c d μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d))).eval x)
      atBot atBot := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuadraticQuadratic a b c d μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_xSubQuadraticQuadratic a b c d μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_odd : Odd P.natDegree := by
    rw [hP_deg]
    norm_num
  exact tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hP_pos hP_deg_pos hP_odd

/-- The normalized quadratic/quadratic x-subtraction polynomial tends to
`+∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticQuadratic_atTop_atTop (a b c d μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuadraticQuadratic a b c d μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_xSubQuadraticQuadratic a b c d μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- Strict order case `a < c < b < d < 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_a_c_b_d
    {a b c d μ : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have had : a < d := lt_trans hac (lt_trans hcb hbd)
  have hc0 : c < 0 := lt_trans hcb (lt_trans hbd hd0)
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (a - c) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hac) (sub_neg.mpr had)
    nlinarith [mul_pos hμ hG]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_pos : 0 < c - a := sub_pos.mpr hac
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_neg : (c - a) * (c - b) < 0 :=
      mul_neg_of_pos_of_neg hca_pos hcb_neg
    have hleft_pos : 0 < c * ((c - a) * (c - b)) :=
      mul_pos_of_neg_of_neg hc0 hprod_neg
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_neg : b - d < 0 := sub_neg.mpr hbd
    have hG_neg : (b - c) * (b - d) < 0 :=
      mul_neg_of_pos_of_neg hbc_pos hbd_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_pos : 0 < d - b := sub_pos.mpr hbd
    have hprod_pos : 0 < (d - a) * (d - b) := mul_pos hda_pos hdb_pos
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, ha_r₁, hr₁_c, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hac
      (mul_neg_of_neg_of_pos hP_a_neg hP_c_pos)
  obtain ⟨r₂, hb_r₂, hr₂_d, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbd
      (mul_neg_of_pos_of_neg hP_b_pos hP_d_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_c (lt_trans hcb hb_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_trans hr₂_d hd0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Strict order case `a < c ≤ d < b ≤ 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_a_c_d_b
    {a b c d μ : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have had : a < d := lt_of_lt_of_le hac hcd
  have hc0 : c < 0 := lt_of_le_of_lt hcd (lt_of_lt_of_le hdb hb0)
  have hd0 : d < 0 := lt_of_lt_of_le hdb hb0
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (a - c) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hac) (sub_neg.mpr had)
    nlinarith [mul_pos hμ hG]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_pos : 0 < c - a := sub_pos.mpr hac
    have hcb_neg : c - b < 0 :=
      sub_neg.mpr (lt_of_le_of_lt hcd hdb)
    have hprod_neg : (c - a) * (c - b) < 0 :=
      mul_neg_of_pos_of_neg hca_pos hcb_neg
    have hleft_pos : 0 < c * ((c - a) * (c - b)) :=
      mul_pos_of_neg_of_neg hc0 hprod_neg
    nlinarith
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr (lt_of_le_of_lt hcd hdb)
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hG : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    nlinarith [mul_pos hμ hG]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, ha_r₁, hr₁_c, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hac
      (mul_neg_of_neg_of_pos hP_a_neg hP_c_pos)
  obtain ⟨r₂, hd_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hdb
      (mul_neg_of_pos_of_neg hP_d_pos hP_b_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_c (lt_of_le_of_lt hcd hd_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_of_lt_of_le hr₂_b hb0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Strict order case `c < a ≤ b < d < 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_c_a_b_d
    {a b c d μ : ℝ} (hca : c < a) (hab : a ≤ b) (hbd : b < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have cad : c < d := lt_trans hca (lt_of_le_of_lt hab hbd)
  have ha0 : a < 0 := lt_of_le_of_lt (hab.trans (le_of_lt hbd)) hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr (lt_of_lt_of_le hca hab)
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr (lt_of_le_of_lt hab hbd)
    have hG_neg : (a - c) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg hac_pos had_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr (lt_of_lt_of_le hca hab)
    have hbd_neg : b - d < 0 := sub_neg.mpr hbd
    have hG_neg : (b - c) * (b - d) < 0 :=
      mul_neg_of_pos_of_neg hbc_pos hbd_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr (lt_of_le_of_lt hab hbd)
    have hdb_pos : 0 < d - b := sub_pos.mpr hbd
    have hprod_pos : 0 < (d - a) * (d - b) := mul_pos hda_pos hdb_pos
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, hb_r₂, hr₂_d, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbd
      (mul_neg_of_pos_of_neg hP_b_pos hP_d_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_of_le_of_lt hab hb_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_trans hr₂_d hd0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Strict order case `c < a < d < b ≤ 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_c_a_d_b
    {a b c d μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have ha0 : a < 0 := lt_trans had (lt_of_lt_of_le hdb hb0)
  have hc0 : c < 0 := lt_trans hca ha0
  have hd0 : d < 0 := lt_of_lt_of_le hdb hb0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr (lt_trans hca (lt_trans had hdb))
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have hG_neg : (a - c) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg hac_pos had_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr (lt_trans hca (lt_trans had hdb))
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hG : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    nlinarith [mul_pos hμ hG]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, hd_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hdb
      (mul_neg_of_pos_of_neg hP_d_pos hP_b_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans had hd_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_of_lt_of_le hr₂_b hb0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- The normalized monic quadratic/quadratic x-subtraction leaf. -/
theorem xSubQuadraticQuadraticSplits :
    xSubQuadraticQuadraticSplitsStatement := by
  intro a b c d μ hab hcd had hcb hb0 hd0 hμ
  by_cases hd_zero : d = 0
  · subst d
    simpa using xSubQuadraticQuadraticSplits_of_right_root_zero
      hab hcb hμ
  by_cases hac_eq : a = c
  · subst c
    exact xSubQuadraticQuadraticSplits_of_common_root
      (r := a) (s := b) (t := d) hb0 hd0 hμ
  by_cases had_eq : a = d
  · subst d
    have hc0 : c ≤ 0 := hcd.trans hd0
    have hsplits := xSubQuadraticQuadraticSplits_of_common_root
      (r := a) (s := b) (t := c) hb0 hc0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hbc_eq : b = c
  · subst c
    have ha0 : a ≤ 0 := hab.trans hb0
    have hsplits := xSubQuadraticQuadraticSplits_of_common_root
      (r := b) (s := a) (t := d) ha0 hd0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hbd_eq : b = d
  · subst d
    have ha0 : a ≤ 0 := hab.trans hb0
    have hc0 : c ≤ 0 := hcd.trans hb0
    have hsplits := xSubQuadraticQuadraticSplits_of_common_root
      (r := b) (s := a) (t := c) ha0 hc0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  have hdlt : d < 0 := lt_of_le_of_ne hd0 hd_zero
  rcases lt_or_gt_of_ne hac_eq with hac | hca
  · rcases lt_or_gt_of_ne hbd_eq with hbd | hdb
    · have hcb_lt : c < b := by
        exact lt_of_le_of_ne hcb (by intro h; exact hbc_eq h.symm)
      exact xSubQuadraticQuadraticSplits_of_order_a_c_b_d
        hac hcb_lt hbd hdlt hμ
    · exact xSubQuadraticQuadraticSplits_of_order_a_c_d_b
        hac hcd hdb hb0 hμ
  · rcases lt_or_gt_of_ne hbd_eq with hbd | hdb
    · exact xSubQuadraticQuadraticSplits_of_order_c_a_b_d
        hca hab hbd hdlt hμ
    · have had_lt : a < d := lt_of_le_of_ne had had_eq
      exact xSubQuadraticQuadraticSplits_of_order_c_a_d_b
        hca had_lt hdb hb0 hμ

/-- The normalized monic quadratic/quadratic x-subtraction leaf implies the
degree-two/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, hab, hproots, hpfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.left_splits hpdeg
  obtain ⟨c, d, hcd, hqroots, hqfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.right_splits hqdeg
  obtain ⟨had, hcb⟩ :=
    roots_overlap_of_positiveSplitRootCountPair_two_two
      hpair hab hcd hproots hqroots
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn b hb_mem
  have hd0 : d ≤ 0 := by
    have hd_mem : d ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn d hd_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] :=
    X * ((X - C a) * (X - C b)) - C ν * ((X - C c) * (X - C d))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hcd had hcb hb0 hd0 hν_pos
  have hpfacA : p = C A * ((X - C a) * (X - C b)) := by
    simpa [A] using hpfac
  have hqfacB : q = C B * ((X - C c) * (X - C d)) := by
    simpa [B] using hqfac
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfacA, hqfacB]
    dsimp [inner, ν]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hA_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-two/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two_of_monic
    xSubQuadraticQuadraticSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-two right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic quadratic/quadratic leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 2 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 2 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 2 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Degree-two right endpoint case for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    xSubQuadraticQuadraticSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree two for the same-degree
sign-normalized x-subtraction leaf, modulo the normalized monic
quadratic/quadratic leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_one : g.natDegree ≤ 1
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
      hpair hfnn hgnn hdeg hle_one
  · have htwo : g.natDegree = 2 := by
      lia
    exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
      hmono hpair hfnn hgnn hdeg htwo

/-- Endpoint cases through right degree two for the same-degree
sign-normalized x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two_of_monic
    xSubQuadraticQuadraticSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-two right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
quadratic/quadratic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-two right endpoint terminal as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
    xSubQuadraticQuadraticSplits

/-- Pack the endpoint cases through degree two as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
quadratic/quadratic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two_of_monic
    hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree two as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 2) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two_of_monic
    xSubQuadraticQuadraticSplits

/-- In the `(2, 3)` positive split root-count case, the roots obey the
finite interleaving inequalities obtained by symmetry from the `(3, 2)` case.
-/
lemma roots_order_of_positiveSplitRootCountPair_two_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c d e : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hde : d ≤ e)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d, e}) :
    c ≤ a ∧ d ≤ b ∧ a ≤ e := by
  exact roots_order_of_positiveSplitRootCountPair_three_two
    h.symm hcd hde hab hgroots hfroots

/-- A `(2, 3)` positive split root-count pair admits ordered root data with
the interleaving inequalities needed by the degree-three right-successor
x-subtraction terminal. -/
lemma exists_roots_order_of_positiveSplitRootCountPair_two_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 3) :
    ∃ a b c d e : ℝ,
      a ≤ b ∧ c ≤ d ∧ d ≤ e ∧
        f.roots = {a, b} ∧ g.roots = {c, d, e} ∧
          f = C f.leadingCoeff * ((X - C a) * (X - C b)) ∧
            g = C g.leadingCoeff * ((X - C c) * (X - C d) * (X - C e)) ∧
              c ≤ a ∧ d ≤ b ∧ a ≤ e := by
  obtain ⟨a, b, hab, hfroots, hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two h.left_splits hfdeg
  obtain ⟨c, d, e, hcd, hde, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.right_splits hgdeg
  obtain ⟨hca, hdb, hae⟩ :=
    roots_order_of_positiveSplitRootCountPair_two_three
      h hab hcd hde hfroots hgroots
  exact
    ⟨a, b, c, d, e, hab, hcd, hde, hfroots, hgroots, hffac, hgfac,
      hca, hdb, hae⟩

/-- In the `(3, 3)` positive split root-count case, neither ordered root list
can contain two roots strictly beyond the next root of the other list.  These
four finite inequalities are the cubic/cubic analogue of the overlap data used
in the quadratic/quadratic endpoint. -/
lemma roots_order_of_positiveSplitRootCountPair_three_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c u v w : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v, w}) :
    u ≤ b ∧ v ≤ c ∧ a ≤ v ∧ b ≤ w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hub
    have hbu : b < u := lt_of_not_ge hub
    let x : ℝ := (b + u) / 2
    have hbx : b < x := by
      dsimp [x]
      linarith
    have hxu : x ≤ u := by
      dsimp [x]
      linarith
    have hax : a < x := lt_of_le_of_lt hab hbx
    have hxv : x ≤ v := hxu.trans huv
    have hxw : x ≤ w := hxv.trans hvw
    have hf_count_le : rootCountAtOrAbove f x ≤ 1 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      by_cases hxc : x ≤ c
      · simp [hnot_xa, hnot_xb, hxc]
      · simp [hnot_xa, hnot_xb, hxc]
    have hg_count : rootCountAtOrAbove g x = 3 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxu, hxv, hxw]
    have hcount := h.count.right_sub_le_one x
    rw [hg_count] at hcount
    norm_num at hcount
    have hf_count_int : ((rootCountAtOrAbove f x : ℤ) ≤ 1) := by
      exact_mod_cast hf_count_le
    linarith
  · by_contra hvc
    have hcv : c < v := lt_of_not_ge hvc
    let x : ℝ := (c + v) / 2
    have hcx : c < x := by
      dsimp [x]
      linarith
    have hxv : x ≤ v := by
      dsimp [x]
      linarith
    have hax : a < x := lt_of_le_of_lt (hab.trans hbc) hcx
    have hbx : b < x := lt_of_le_of_lt hbc hcx
    have hxw : x ≤ w := hxv.trans hvw
    have hf_count : rootCountAtOrAbove f x = 0 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      have hnot_xc : ¬ x ≤ c := not_le.mpr hcx
      simp [hnot_xa, hnot_xb, hnot_xc]
    have hg_count_ge : 2 ≤ rootCountAtOrAbove g x := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxu : x ≤ u
      · simp [hxu, hxv, hxw]
      · simp [hxu, hxv, hxw]
    have hcount := h.count.right_sub_le_one x
    rw [hf_count] at hcount
    norm_num at hcount
    have hg_count_int : (2 : ℤ) ≤ rootCountAtOrAbove g x := by
      exact_mod_cast hg_count_ge
    linarith
  · by_contra hav
    have hva : v < a := lt_of_not_ge hav
    let x : ℝ := (a + v) / 2
    have hxa : x ≤ a := by
      dsimp [x]
      linarith
    have hvx : v < x := by
      dsimp [x]
      linarith
    have hxb : x ≤ b := hxa.trans hab
    have hxc : x ≤ c := hxb.trans hbc
    have hux : u < x := lt_of_le_of_lt huv hvx
    have hf_count : rootCountAtOrAbove f x = 3 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxa, hxb, hxc]
    have hg_count_le : rootCountAtOrAbove g x ≤ 1 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      have hnot_xv : ¬ x ≤ v := not_le.mpr hvx
      by_cases hxw : x ≤ w
      · simp [hnot_xu, hnot_xv, hxw]
      · simp [hnot_xu, hnot_xv, hxw]
    have hcount := h.count.left_sub_le_one x
    rw [hf_count] at hcount
    norm_num at hcount
    have hg_count_int : ((rootCountAtOrAbove g x : ℤ) ≤ 1) := by
      exact_mod_cast hg_count_le
    linarith
  · by_contra hbw
    have hwb : w < b := lt_of_not_ge hbw
    let x : ℝ := (b + w) / 2
    have hxb : x ≤ b := by
      dsimp [x]
      linarith
    have hwx : w < x := by
      dsimp [x]
      linarith
    have hxc : x ≤ c := hxb.trans hbc
    have hux : u < x := lt_of_le_of_lt (huv.trans hvw) hwx
    have hvx : v < x := lt_of_le_of_lt hvw hwx
    have hf_count_ge : 2 ≤ rootCountAtOrAbove f x := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxa : x ≤ a
      · simp [hxa, hxb, hxc]
      · simp [hxa, hxb, hxc]
    have hg_count : rootCountAtOrAbove g x = 0 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      have hnot_xv : ¬ x ≤ v := not_le.mpr hvx
      have hnot_xw : ¬ x ≤ w := not_le.mpr hwx
      simp [hnot_xu, hnot_xv, hnot_xw]
    have hcount := h.count.left_sub_le_one x
    rw [hg_count] at hcount
    norm_num at hcount
    have hf_count_int : (2 : ℤ) ≤ rootCountAtOrAbove f x := by
      exact_mod_cast hf_count_ge
    linarith

/-- A `(3, 3)` positive split root-count pair admits ordered root data with
the four finite inequalities needed by the cubic/cubic x-subtraction endpoint.
-/
lemma exists_roots_order_of_positiveSplitRootCountPair_three_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3) :
    ∃ a b c u v w : ℝ,
      a ≤ b ∧ b ≤ c ∧ u ≤ v ∧ v ≤ w ∧
        f.roots = {a, b, c} ∧ g.roots = {u, v, w} ∧
          f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) ∧
            g = C g.leadingCoeff * ((X - C u) * (X - C v) * (X - C w)) ∧
              u ≤ b ∧ v ≤ c ∧ a ≤ v ∧ b ≤ w := by
  obtain ⟨a, b, c, hab, hbc, hfroots, hffac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.left_splits hfdeg
  obtain ⟨u, v, w, huv, hvw, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.right_splits hgdeg
  obtain ⟨hub, hvc, hav, hbw⟩ :=
    roots_order_of_positiveSplitRootCountPair_three_three
      h hab hbc huv hvw hfroots hgroots
  exact
    ⟨a, b, c, u, v, w, hab, hbc, huv, hvw, hfroots, hgroots,
      hffac, hgfac, hub, hvc, hav, hbw⟩

/-- Normalized monic arithmetic leaf for the degree-three/degree-three
same-degree positive-split x-subtraction endpoint.  The finite root-order
inequalities are exactly those supplied by a `(3, 3)`
`PositiveSplitRootCountPair`. -/
def xSubCubicCubicSplitsStatement : Prop :=
  ∀ {a b c u v w μ : ℝ},
    a ≤ b → b ≤ c → u ≤ v → v ≤ w →
      u ≤ b → v ≤ c → a ≤ v → b ≤ w →
        c ≤ 0 → w ≤ 0 → 0 < μ →
          (X * ((X - C a) * (X - C b) * (X - C c)) -
              C μ * ((X - C u) * (X - C v) * (X - C w))).Splits

/-- The normalized cubic/cubic x-subtraction polynomial is a genuine quartic. -/
lemma natDegree_xSubCubicCubic (a b c u v w μ : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).natDegree = 4 := by
  compute_degree <;> norm_num

/-- The normalized cubic/cubic x-subtraction polynomial is nonzero. -/
lemma xSubCubicCubic_ne_zero (a b c u v w μ : ℝ) :
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubCubicCubic a b c u v w μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized cubic/cubic x-subtraction polynomial has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_xSubCubicCubic (a b c u v w μ : ℝ) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v) * (X - C w))) := by
  have hcubic_pos : HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c)) := by
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hleft_pos : HasPosLeadingCoeff (X * ((X - C a) * (X - C b) * (X - C c))) :=
    hcubic_pos.X_mul
  have hleft_deg :
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree = 4 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v) * (X - C w))).natDegree <
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt :
      degree (C μ * ((X - C u) * (X - C v) * (X - C w))) <
        degree (X * ((X - C a) * (X - C b) * (X - C c))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized cubic/cubic x-subtraction leaf. -/
lemma eval_xSubCubicCubic (a b c u v w μ x : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).eval x =
      x * ((x - a) * (x - b) * (x - c)) -
        μ * ((x - u) * (x - v) * (x - w)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The normalized cubic/cubic x-subtraction polynomial tends to `+∞` at
`-∞`. -/
lemma tendsto_eval_xSubCubicCubic_atBot_atTop (a b c u v w μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v) * (X - C w))).eval x)
      atBot atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_even : Even P.natDegree := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
    norm_num
  exact tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hP_pos hP_deg_pos hP_even

/-- The normalized cubic/cubic x-subtraction polynomial tends to `+∞` at
`+∞`. -/
lemma tendsto_eval_xSubCubicCubic_atTop_atTop (a b c u v w μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v) * (X - C w))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- A cubic whose roots lie between consecutive roots of the quartic
`X * (X - a) * (X - b) * (X - c)` interlaces that quartic. -/
lemma interlaces_cubic_quartic_of_roots_between {a b c u v w : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc0 : c ≤ 0)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hw0 : w ≤ 0) :
    Interlaces ((X - C u) * (X - C v) * (X - C w))
      (X * ((X - C a) * (X - C b) * (X - C c))) := by
  let f : ℝ[X] := X * ((X - C a) * (X - C b) * (X - C c))
  let g : ℝ[X] := (X - C u) * (X - C v) * (X - C w)
  have hf_ne : f ≠ 0 := by
    dsimp [f]
    exact mul_ne_zero X_ne_zero
      (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b))
        (X_sub_C_ne_zero c))
  have hg_ne : g ≠ 0 := by
    dsimp [g]
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero u) (X_sub_C_ne_zero v))
      (X_sub_C_ne_zero w)
  have hf_split : f.Splits := by
    dsimp [f]
    exact Polynomial.Splits.X.mul
      (((Polynomial.Splits.X_sub_C a).mul (Polynomial.Splits.X_sub_C b)).mul
        (Polynomial.Splits.X_sub_C c))
  have hg_split : g.Splits := by
    dsimp [g]
    exact ((Polynomial.Splits.X_sub_C u).mul (Polynomial.Splits.X_sub_C v)).mul
      (Polynomial.Splits.X_sub_C w)
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    compute_degree <;> norm_num
  have hg_deg : g.natDegree = 3 := by
    dsimp [g]
    compute_degree <;> norm_num
  have hf_roots : (↑[a, b, c, 0] : Multiset ℝ) = f.roots := by
    dsimp [f] at hf_ne ⊢
    rw [roots_mul hf_ne, roots_X,
      roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a)
        (X_sub_C_ne_zero b)) (X_sub_C_ne_zero c)),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    change ({a} : Multiset ℝ) + {b} + {c} + {0} =
      ({0} : Multiset ℝ) + ({a} + {b} + {c})
    ac_rfl
  have hg_roots : (↑[u, v, w] : Multiset ℝ) = g.roots := by
    dsimp [g] at hg_ne ⊢
    rw [roots_mul hg_ne, roots_mul (mul_ne_zero (X_sub_C_ne_zero u)
        (X_sub_C_ne_zero v)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    rfl
  change Interlaces g f
  exact Interlaces.of_cubic_quartic_root_lists
    hf_ne hf_split hg_ne hg_split hf_deg hg_deg hf_roots.symm hg_roots.symm
    hab hbc hc0 huv hvw hau hub hbv hvc hcw hw0

/-- In the ordinary interlacing subcase of the normalized cubic/cubic leaf, the
desired splitting follows from the Ma--Wang weak-sign theorem. -/
lemma xSubCubicCubicSplits_of_interlacing_roots {a b c u v w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc0 : c ≤ 0)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let f : ℝ[X] := X * ((X - C a) * (X - C b) * (X - C c))
  let g : ℝ[X] := (X - C u) * (X - C v) * (X - C w)
  have hgf : Interlaces g f := by
    dsimp [f, g]
    exact interlaces_cubic_quartic_of_roots_between
      hab hbc hc0 huv hvw hau hub hbv hvc hcw hw0
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    compute_degree <;> norm_num
  have hF_deg : ((1 : ℝ[X]) * f + (-C μ) * g).natDegree = 4 := by
    dsimp [f, g]
    simpa [sub_eq_add_neg] using natDegree_xSubCubicCubic a b c u v w μ
  have hg_pos : HasPosLeadingCoeff g := by
    dsimp [g]
    exact ((hasPosLeadingCoeff_X_sub_C u).mul (hasPosLeadingCoeff_X_sub_C v)).mul
      (hasPosLeadingCoeff_X_sub_C w)
  have hF_pos : HasPosLeadingCoeff ((1 : ℝ[X]) * f + (-C μ) * g) := by
    dsimp [f, g]
    simpa [sub_eq_add_neg] using hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hdeg_lo : f.natDegree ≤ ((1 : ℝ[X]) * f + (-C μ) * g).natDegree := by
    rw [hf_deg, hF_deg]
  have hdeg_hi : ((1 : ℝ[X]) * f + (-C μ) * g).natDegree ≤ f.natDegree + 1 := by
    rw [hf_deg, hF_deg]
    norm_num
  have hb_nonpos : ∀ r, f.IsRoot r → (-C μ).eval r ≤ 0 := by
    intro r _
    simpa only [eval_neg, eval_C, Left.neg_nonpos_iff] using le_of_lt hμ
  have hprec : Prec f ((1 : ℝ[X]) * f + (-C μ) * g) :=
    prec_of_interlaces_evalCoeff_nonpos
      hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  have hsplits : ((1 : ℝ[X]) * f + (-C μ) * g).Splits := hprec.2.1.2
  dsimp [f, g] at hsplits ⊢
  simpa [sub_eq_add_neg] using hsplits

/-- If the normalized cubic/cubic x-subtraction endpoints share a linear
factor, the splitting problem reduces to the already proved
quadratic/quadratic leaf. -/
lemma xSubCubicCubicSplits_of_common_root {r a b c d μ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (had : a ≤ d) (hcb : c ≤ b)
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * ((X - C a) * (X - C b))) -
      C μ * ((X - C r) * ((X - C c) * (X - C d)))).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C b)) -
    C μ * ((X - C c) * (X - C d))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact xSubQuadraticQuadraticSplits hab hcd had hcb hb0 hd0 hμ
  have hfactor :
      X * ((X - C r) * ((X - C a) * (X - C b))) -
        C μ * ((X - C r) * ((X - C c) * (X - C d))) =
        (X - C r) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hQ

/-- Boundary case of the normalized cubic/cubic leaf where the lower
right-endpoint root equals the lower left-endpoint root. -/
lemma xSubCubicCubicSplits_of_lower_common_root {a b c v w μ : ℝ}
    (hbc : b ≤ c) (hvw : v ≤ w) (hvc : v ≤ c) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C a) * (X - C v) * (X - C w))).Splits := by
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := a) (a := b) (b := c) (c := v) (d := w)
    hbc hvw hbw hvc hc0 hw0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

/-- Boundary case of the normalized cubic/cubic leaf where the middle
right-endpoint root equals the middle left-endpoint root. -/
lemma xSubCubicCubicSplits_of_middle_common_root {a b c u w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hub : u ≤ b) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C b) * (X - C w))).Splits := by
  have hac : a ≤ c := hab.trans hbc
  have huw : u ≤ w := hub.trans hbw
  have haw : a ≤ w := hab.trans hbw
  have huc : u ≤ c := hub.trans hbc
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := b) (a := a) (b := c) (c := u) (d := w)
    hac huw haw huc hc0 hw0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

/-- Boundary case of the normalized cubic/cubic leaf where the upper
right-endpoint root equals the upper left-endpoint root. -/
lemma xSubCubicCubicSplits_of_upper_common_root {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v) (hub : u ≤ b)
    (hav : a ≤ v) (hvc : v ≤ c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C c))).Splits := by
  have hb0 : b ≤ 0 := hbc.trans hc0
  have hv0 : v ≤ 0 := hvc.trans hc0
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := c) (a := a) (b := b) (c := u) (d := v)
    hab huv hav hub hb0 hv0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf where the
left root of the right endpoint lies left of the left endpoint roots, and the
last right-endpoint root still lies before the upper left endpoint root:
`u < a < v < b < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_v_b_w_c {a b c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvb : v < b) (hbw : b < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hav hvb
  have hac : a < c := lt_trans hab (lt_trans hbw hwc)
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hvc : v < c := lt_trans hvb (lt_trans hbw hwc)
  have hb0 : b < 0 := lt_of_lt_of_le (lt_trans hbw hwc) hc0
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    have hleft_neg : v * ((v - a) * (v - b) * (v - c)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - b) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos h12_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hvb hwc hav hbw hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`u < a < v < b < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_v_b_c_w {a b c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvb : v < b) (hbc : b < c)
    (hcw : c < w) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hav hvb
  have hac : a < c := lt_trans hab hbc
  have haw : a < w := lt_trans hac hcw
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hvc : v < c := lt_trans hvb hbc
  have hbw : b < w := lt_trans hbc hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans hbc hc0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    have hleft_neg : v * ((v - a) * (v - b) * (v - c)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos (mul_pos hwa_pos hwb_pos) hwc_pos
    have hleft_neg : w * ((w - a) * (w - b) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hvb hcw hav hbc (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`u < a < b < v < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_b_v_w_c {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbv : b < v) (hvw : v < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hac : a < c := lt_trans hab (lt_trans hbv (lt_trans hvw hwc))
  have haw : a < w := lt_trans hab (lt_trans hbv hvw)
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hvc : v < c := lt_trans hvw hwc
  have hbw : b < w := lt_trans hbv hvw
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hv0 : v < 0 := lt_trans hvw hw0
  have hb0 : b < 0 := lt_trans hbv hv0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hab hbv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hab hbv)
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - b) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos h12_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hbv hwc hab hvw hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`u < a < b < v < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_b_v_c_w {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbv : b < v) (hvc : v < c)
    (hcw : c < w) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hac : a < c := lt_trans hab (lt_trans hbv hvc)
  have haw : a < w := lt_trans hac hcw
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hbw : b < w := lt_trans (lt_trans hbv hvc) hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans (lt_trans hbv hvc) hc0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_trans hvc hc0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hab hbv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hab hbv)
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos (mul_pos hwa_pos hwb_pos) hwc_pos
    have hleft_neg : w * ((w - a) * (w - b) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hbv hcw hab hvc (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Dispatcher for the strict left-outlier cubic/cubic subcases with no middle
boundary equalities.  The four branches correspond to the positions of `v`
relative to `b` and `w` relative to `c`. -/
lemma xSubCubicCubicSplits_of_left_root_left_strict_distinct {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbc : b < c)
    (hav : a < v) (hvc : v < c) (hvw : v < w) (hbw : b < w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hvb_ne : v ≠ b) (hwc_ne : w ≠ c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  rcases lt_or_gt_of_ne hvb_ne with hvb | hbv
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_u_a_v_b_w_c
        hua hav hvb hbw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_order_u_a_v_b_c_w
        hua hav hvb hbc hcw hw0 hμ
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_u_a_b_v_w_c
        hua hab hbv hvw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_order_u_a_b_v_c_w
        hua hab hbv hvc hcw hw0 hμ

/-- Dispatcher for the strict left-outlier cubic/cubic subcases with weak
middle boundary inequalities.  Boundary equalities reduce to the common-root
quadratic/quadratic endpoint; the remaining case is the strict dispatcher. -/
lemma xSubCubicCubicSplits_of_left_root_left_strict_roots {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbc : b < c)
    (hav : a ≤ v) (hvc : v ≤ c) (hvw : v < w) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hva : v = a
  · subst v
    have huw : u ≤ w := by
      exact (le_of_lt hua).trans ((le_of_lt hab).trans hbw)
    have huc : u ≤ c := by
      exact (le_of_lt hua).trans ((le_of_lt hab).trans (le_of_lt hbc))
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := a) (a := b) (b := c) (c := u) (d := w)
      (le_of_lt hbc) huw hbw huc hc0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hvb : v = b
  · subst v
    have hub : u ≤ b := (le_of_lt hua).trans (le_of_lt hab)
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_of_lt hbc) hub hbw hc0 (le_of_lt hw0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have huw : u ≤ w := by
      exact (le_of_lt hua).trans ((le_of_lt hab).trans hbw)
    have haw : a ≤ w := (le_of_lt hab).trans hbw
    have hub : u ≤ b := (le_of_lt hua).trans (le_of_lt hab)
    have hb0 : b ≤ 0 := (le_of_lt hbc).trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := c) (a := a) (b := b) (c := u) (d := w)
      (le_of_lt hab) huw haw hub hb0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwb : w = b
  · subst w
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have huv : u ≤ v := (le_of_lt hua).trans hav
    have huc : u ≤ c := by
      exact (le_of_lt hua).trans ((le_of_lt hab).trans (le_of_lt hbc))
    have hv0 : v ≤ 0 := hvc.trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := u) (d := v)
      hac huv hav huc hc0 hv0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc : w = c
  · subst w
    have huv : u ≤ v := (le_of_lt hua).trans hav
    have hub : u ≤ b := (le_of_lt hua).trans (le_of_lt hab)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) huv hub hav hvc hc0 hμ
  have hav_lt : a < v := by
    exact lt_of_le_of_ne hav (by intro h; exact hva h.symm)
  have hvc_lt : v < c := by
    exact lt_of_le_of_ne hvc hvc_eq
  have hbw_lt : b < w := by
    exact lt_of_le_of_ne hbw (by intro h; exact hwb h.symm)
  exact xSubCubicCubicSplits_of_left_root_left_strict_distinct
    hua hab hbc hav_lt hvc_lt hvw hbw_lt hc0 hw0 hvb hwc hμ

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`a < u < b < v < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_b_v_w_c {a b c u v w μ : ℝ}
    (hau : a < u) (hub : u < b) (hbv : b < v) (hvw : v < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hau hub
  have hac : a < c := lt_trans hab (lt_trans hbv (lt_trans hvw hwc))
  have huv : u < v := lt_trans hub hbv
  have huc : u < c := lt_trans hub (lt_trans hbv (lt_trans hvw hwc))
  have hbc : b < c := lt_trans hbv (lt_trans hvw hwc)
  have hvc : v < c := lt_trans hvw hwc
  have hb0 : b < 0 := lt_of_lt_of_le hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hau huv)
    have haw_neg : a - w < 0 := sub_neg.mpr (lt_trans (lt_trans hau huv) hvw)
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr (lt_trans hbv hvw)
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hab hbv)
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr (lt_trans (lt_trans hab hbv) hvw)
    have hwb_pos : 0 < w - b := sub_pos.mpr (lt_trans hbv hvw)
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - b) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos h12_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hau hbv hwc hub hvw hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`a < u < v < b < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_v_b_c_w {a b c u v w μ : ℝ}
    (hau : a < u) (huv : u < v) (hvb : v < b) (hbc : b < c)
    (hcw : c < w) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans (lt_trans hau huv) hvb
  have hac : a < c := lt_trans hab hbc
  have haw : a < w := lt_trans hac hcw
  have hub : u < b := lt_trans huv hvb
  have huc : u < c := lt_trans hub hbc
  have hvw : v < w := lt_trans hvb (lt_trans hbc hcw)
  have hvc : v < c := lt_trans hvb hbc
  have hbw : b < w := lt_trans hbc hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hau huv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hau huv)
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    have hleft_neg : v * ((v - a) * (v - b) * (v - c)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos (mul_pos hwa_pos hwb_pos) hwc_pos
    have hleft_neg : w * ((w - a) * (w - b) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hau hvb hcw huv hbc (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`a < u < v < b < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_v_b_w_c {a b c u v w μ : ℝ}
    (hau : a < u) (huv : u < v) (hvb : v < b) (hbw : b < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans (lt_trans hau huv) hvb
  have hac : a < c := lt_trans hab (lt_trans hbw hwc)
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_trans huv hvb
  have huc : u < c := lt_trans hub (lt_trans hbw hwc)
  have hvc : v < c := lt_trans hvb (lt_trans hbw hwc)
  have hbc : b < c := lt_trans hbw hwc
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hb0 : b < 0 := lt_trans hbw hw0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hau huv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hau huv)
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    have hleft_neg : v * ((v - a) * (v - b) * (v - c)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - b) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos h12_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hau hvb hwc huv hbw hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u = v < b < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_u_b_w_c {a b c u w μ : ℝ}
    (hau : a < u) (hub : u < b) (hbw : b < w) (hwc : w < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))
  have hab : a < b := lt_trans hau hub
  have haw : a < w := lt_trans hab hbw
  have huc : u < c := lt_trans hub (lt_trans hbw hwc)
  have hbc : b < c := lt_trans hbw hwc
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hb0 : b < 0 := lt_trans hbw hw0
  have hu0 : u < 0 := lt_trans hub hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hsq_pos : 0 < (a - u) * (a - u) :=
      mul_pos_of_neg_of_neg hau_neg hau_neg
    have hG_neg : (a - u) * (a - u) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hsq_pos : 0 < (b - u) * (b - u) := mul_pos hbu_pos hbu_pos
    have hG_neg : (b - u) * (b - u) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - b) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have hsq_pos : 0 < (c - u) * (c - u) := mul_pos hcu_pos hcu_pos
    have hG_pos : 0 < (c - u) * (c - u) * (c - w) :=
      mul_pos hsq_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hsq_pos : 0 < (0 - u) * (0 - u) := mul_pos h0u_pos h0u_pos
    have hG_pos : 0 < (0 - u) * (0 - u) * (0 - w) :=
      mul_pos hsq_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u u w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u u w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hub hwc (le_refl u) (le_of_lt hbw) hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u = v < b < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_u_b_c_w {a b c u w μ : ℝ}
    (hau : a < u) (hub : u < b) (hbc : b < c) (hcw : c < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))
  have hab : a < b := lt_trans hau hub
  have hac : a < c := lt_trans hab hbc
  have haw : a < w := lt_trans hac hcw
  have huc : u < c := lt_trans hub hbc
  have hbw : b < w := lt_trans hbc hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hsq_pos : 0 < (a - u) * (a - u) :=
      mul_pos_of_neg_of_neg hau_neg hau_neg
    have hG_neg : (a - u) * (a - u) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hsq_pos : 0 < (b - u) * (b - u) := mul_pos hbu_pos hbu_pos
    have hG_neg : (b - u) * (b - u) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have hsq_pos : 0 < (c - u) * (c - u) := mul_pos hcu_pos hcu_pos
    have hG_neg : (c - u) * (c - u) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos (mul_pos hwa_pos hwb_pos) hwc_pos
    have hleft_neg : w * ((w - a) * (w - b) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hsq_pos : 0 < (0 - u) * (0 - u) := mul_pos h0u_pos h0u_pos
    have hG_pos : 0 < (0 - u) * (0 - u) * (0 - w) :=
      mul_pos hsq_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u u w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u u w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hub hcw (le_refl u) (le_of_lt hbc) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-left-root boundary package for the repeated lower right root
`u = v`.  The endpoint coincidences `w = b` and `w = c` reduce to common-root
quadratic/quadratic endpoints; the remaining two orders use adjacent
sign-change intervals. -/
lemma xSubCubicCubicSplits_of_lower_right_double_root {a b c u w μ : ℝ}
    (hab : a < b) (hbc : b < c) (hau : a < u) (hub : u < b)
    (hbw : b ≤ w) (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))).Splits := by
  by_cases hwb : w = b
  · subst w
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have huc : u ≤ c := (le_of_lt hub).trans (le_of_lt hbc)
    have hu0 : u ≤ 0 :=
      (le_of_lt hub).trans ((le_of_lt hbc).trans hc0)
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := u) (d := u)
      hac (le_refl u) (le_of_lt hau) huc hc0 hu0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc : w = c
  · subst w
    have huc : u ≤ c := (le_of_lt hub).trans (le_of_lt hbc)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) (le_refl u) (le_of_lt hub)
      (le_of_lt hau) huc hc0 hμ
  by_cases hwc_lt : w < c
  · have hbw_lt : b < w := lt_of_le_of_ne hbw (by intro h; exact hwb h.symm)
    exact xSubCubicCubicSplits_of_order_a_u_u_b_w_c
      hau hub hbw_lt hwc_lt hc0 hμ
  · have hcw : c < w :=
      lt_of_le_of_ne (le_of_not_gt hwc_lt) (by intro h; exact hwc h.symm)
    exact xSubCubicCubicSplits_of_order_a_u_u_b_c_w
      hau hub hbc hcw hw0 hμ

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a < b < v = w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_b_v_v_c {a b c u v μ : ℝ}
    (hua : u < a) (hab : a < b) (hbv : b < v) (hvc : v < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))
  have hac : a < c := lt_trans hab (lt_trans hbv hvc)
  have hav : a < v := lt_trans hab hbv
  have huc : u < c := lt_trans hua hac
  have ha0 : a < 0 := lt_of_lt_of_le hac hc0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr (lt_trans hua hab)
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hsq_pos : 0 < (a - v) * (a - v) :=
      mul_pos_of_neg_of_neg hav_neg hav_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - v)) :=
      mul_pos hau_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr (lt_trans hua hab)
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hsq_pos : 0 < (b - v) * (b - v) :=
      mul_pos_of_neg_of_neg hbv_neg hbv_neg
    have hG_pos : 0 < (b - u) * ((b - v) * (b - v)) :=
      mul_pos hbu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hsq_pos : 0 < (c - v) * (c - v) := mul_pos hcv_pos hcv_pos
    have hG_pos : 0 < (c - u) * ((c - v) * (c - v)) :=
      mul_pos hcu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have hsq_pos : 0 < (0 - v) * (0 - v) := mul_pos h0v_pos h0v_pos
    have hG_pos : 0 < (0 - u) * ((0 - v) * (0 - v)) :=
      mul_pos h0u_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v v μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v v μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hbv hvc (le_of_lt hab) (le_refl v) hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u < b < v = w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_b_v_v_c {a b c u v μ : ℝ}
    (hau : a < u) (hub : u < b) (hbv : b < v) (hvc : v < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))
  have hab : a < b := lt_trans hau hub
  have hav : a < v := lt_trans hab hbv
  have huc : u < c := lt_trans hub (lt_trans hbv hvc)
  have hbc : b < c := lt_trans hbv hvc
  have hb0 : b < 0 := lt_of_lt_of_le hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hsq_pos : 0 < (a - v) * (a - v) :=
      mul_pos_of_neg_of_neg hav_neg hav_neg
    have hG_neg : (a - u) * ((a - v) * (a - v)) < 0 :=
      mul_neg_of_neg_of_pos hau_neg hsq_pos
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hsq_pos : 0 < (b - v) * (b - v) :=
      mul_pos_of_neg_of_neg hbv_neg hbv_neg
    have hG_pos : 0 < (b - u) * ((b - v) * (b - v)) :=
      mul_pos hbu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hsq_pos : 0 < (c - v) * (c - v) := mul_pos hcv_pos hcv_pos
    have hG_pos : 0 < (c - u) * ((c - v) * (c - v)) :=
      mul_pos hcu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have hsq_pos : 0 < (0 - v) * (0 - v) := mul_pos h0v_pos h0v_pos
    have hG_pos : 0 < (0 - u) * ((0 - v) * (0 - v)) :=
      mul_pos h0u_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v v μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v v μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hbv hvc (le_of_lt hub) (le_refl v) hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-left-root boundary package for the repeated upper right root
`v = w`.  Endpoint coincidences reduce to common-root quadratic/quadratic
endpoints; the remaining two orders use adjacent sign-change intervals. -/
lemma xSubCubicCubicSplits_of_upper_right_double_root {a b c u v μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u < v) (hub : u ≤ b)
    (hvc : v ≤ c) (hav : a ≤ v) (hbv : b ≤ v)
    (hc0 : c ≤ 0) (hv0 : v < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))).Splits := by
  by_cases hvb_eq : v = b
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_of_lt hbc) hub (le_refl b)
      hc0 (le_of_lt hv0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt huv) hub hac (le_refl c) hc0 hμ
  have hbv_lt : b < v :=
    lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  by_cases hua : u < a
  · exact xSubCubicCubicSplits_of_order_u_a_b_v_v_c
      hua hab hbv_lt hvc_lt hc0 hμ
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_of_lt hbc) (le_refl v) hvc hbv hc0 (le_of_lt hv0) hμ
  by_cases hub_eq : u = b
  · subst u
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := v) (d := v)
      hac (le_refl v) hav hvc hc0 (le_of_lt hv0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  have hau : a < u :=
    lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
  have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
  exact xSubCubicCubicSplits_of_order_a_u_b_v_v_c
    hau hub_lt hbv_lt hvc_lt hc0 hμ

/-- Dispatcher for the strict cubic/cubic subcases where the lower right root
lies strictly between the lower and middle left roots.  The ordinary branch is
closed by Ma--Wang interlacing; the other three branches are the strict
nonordinary sign-change lemmas. -/
lemma xSubCubicCubicSplits_of_left_root_right_strict_distinct {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (hau : a < u) (hub : u < b)
    (huv : u < v) (hvw : v < w) (hvc : v < c) (hbw : b < w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hvb_ne : v ≠ b) (hwc_ne : w ≠ c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  rcases lt_or_gt_of_ne hvb_ne with hvb | hbv
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_a_u_v_b_w_c
        hau huv hvb hbw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_order_a_u_v_b_c_w
        hau huv hvb hbc hcw hw0 hμ
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_a_u_b_v_w_c
        hau hub hbv hvw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_interlacing_roots
        (le_of_lt hab) (le_of_lt hbc) hc0
        (le_of_lt huv) (le_of_lt hvw) (le_of_lt hau) (le_of_lt hub)
        (le_of_lt hbv) (le_of_lt hvc) (le_of_lt hcw) (le_of_lt hw0) hμ

/-- Dispatcher for the strict cubic/cubic subcases where the lower right root
lies weakly between the lower and middle left roots.  Boundary equalities reduce
to common-root quadratic/quadratic endpoints; the remaining case is the strict
dispatcher. -/
lemma xSubCubicCubicSplits_of_left_root_right_strict_roots {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (hau : a < u) (hub : u ≤ b)
    (huv : u < v) (hvw : v < w) (hvc : v ≤ c) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hub_eq : u = b
  · subst u
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have haw : a ≤ w := (le_of_lt hab).trans hbw
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := v) (d := w)
      hac (le_of_lt hvw) haw hvc hc0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hvb : v = b
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_of_lt hbc) hub hbw hc0 (le_of_lt hw0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have huw : u ≤ w := (le_of_lt huv).trans (le_of_lt hvw)
    have haw : a ≤ w := (le_of_lt hab).trans hbw
    have hb0 : b ≤ 0 := (le_of_lt hbc).trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := c) (a := a) (b := b) (c := u) (d := w)
      (le_of_lt hab) huw haw hub hb0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwb : w = b
  · subst w
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have hav : a ≤ v := (le_of_lt hau).trans (le_of_lt huv)
    have huc : u ≤ c := hub.trans (le_of_lt hbc)
    have hv0 : v ≤ 0 := hvc.trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := u) (d := v)
      hac (le_of_lt huv) hav huc hc0 hv0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc : w = c
  · subst w
    have hav : a ≤ v := (le_of_lt hau).trans (le_of_lt huv)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt huv) hub hav hvc
      hc0 hμ
  have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  have hbw_lt : b < w := by
    exact lt_of_le_of_ne hbw (by intro h; exact hwb h.symm)
  exact xSubCubicCubicSplits_of_left_root_right_strict_distinct
    hab hbc hau hub_lt huv hvw hvc_lt hbw_lt hc0 hw0 hvb hwc hμ

/-- Strict-root dispatcher for the normalized cubic/cubic leaf with negative
upper endpoints.  It splits on the lower right root relative to the lower left
root and reuses the two strict packages plus the common-root boundary. -/
lemma xSubCubicCubicSplits_of_strict_roots {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u < v) (hvw : v < w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hua : u < a
  · exact xSubCubicCubicSplits_of_left_root_left_strict_roots
      hua hab hbc hav hvc hvw hbw hc0 hw0 hμ
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_of_lt hbc) (le_of_lt hvw) hvc hbw hc0 (le_of_lt hw0) hμ
  have hau : a < u := by
    exact lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
  exact xSubCubicCubicSplits_of_left_root_right_strict_roots
    hab hbc hau hub huv hvw hvc hbw hc0 hw0 hμ

/-- Strict-left-root dispatcher for the normalized cubic/cubic leaf with a weak
lower-right-root inequality.  The boundary `u = v` is the repeated lower
right-root package; the strict case reuses `xSubCubicCubicSplits_of_strict_roots`.
-/
lemma xSubCubicCubicSplits_of_strict_left_roots_right_upper_strict
    {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u ≤ v) (hvw : v < w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases huv_eq : u = v
  · subst v
    by_cases hua : u = a
    · subst u
      exact xSubCubicCubicSplits_of_lower_common_root
        (le_of_lt hbc) (le_of_lt hvw) hvc hbw hc0 (le_of_lt hw0) hμ
    by_cases hub_eq : u = b
    · subst u
      exact xSubCubicCubicSplits_of_middle_common_root
        (le_of_lt hab) (le_of_lt hbc) (le_refl b) hbw
        hc0 (le_of_lt hw0) hμ
    have hau : a < u := lt_of_le_of_ne hav (by intro h; exact hua h.symm)
    have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
    exact xSubCubicCubicSplits_of_lower_right_double_root
      hab hbc hau hub_lt hbw hc0 hw0 hμ
  · have huv_lt : u < v := lt_of_le_of_ne huv huv_eq
    exact xSubCubicCubicSplits_of_strict_roots
      hab hbc huv_lt hvw hub hvc hav hbw hc0 hw0 hμ

/-- Normalized cubic/cubic leaf with strict left roots, weak right-root order,
and strictly negative upper endpoints.  The `v = w` boundary is the repeated
upper right-root package; the strict `v < w` case reuses the previous wrapper.
-/
lemma xSubCubicCubicSplits_of_strict_left_roots {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hvw_eq : v = w
  · subst w
    by_cases huv_eq : u = v
    · subst v
      have hub_eq : u = b := le_antisymm hub hbw
      subst u
      exact xSubCubicCubicSplits_of_middle_common_root
        (le_of_lt hab) (le_of_lt hbc) (le_refl b) (le_refl b)
        hc0 (le_of_lt hw0) hμ
    · have huv_lt : u < v := lt_of_le_of_ne huv huv_eq
      exact xSubCubicCubicSplits_of_upper_right_double_root
        hab hbc huv_lt hub hvc hav hbw hc0 hw0 hμ
  · have hvw_lt : v < w := lt_of_le_of_ne hvw hvw_eq
    exact xSubCubicCubicSplits_of_strict_left_roots_right_upper_strict
      hab hbc huv hvw_lt hub hvc hav hbw hc0 hw0 hμ

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a = b < v ≤ w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_a_v_w_c {a c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvw : v ≤ w) (hwc : w < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have haw : a < w := lt_of_lt_of_le hav hvw
  have huc : u < c := lt_trans hua (lt_trans haw hwc)
  have hvc : v < c := lt_of_le_of_lt hvw hwc
  have ha0 : a < 0 := lt_of_lt_of_le (lt_trans haw hwc) hc0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hsq_pos : 0 < (u - a) * (u - a) :=
      mul_pos_of_neg_of_neg hua_neg hua_neg
    have hprod_neg : (u - a) * (u - a) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - a) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have htail_pos : 0 < (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg hav_neg haw_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - w)) :=
      mul_pos hau_pos htail_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
    have hprod_neg : (v - a) * (v - a) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - a) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
    have hprod_neg : (w - a) * (w - a) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - a) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have hhead_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos hhead_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a a c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a a c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hav hwc (le_refl a) hvw hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_a_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a = b < v < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_a_v_c_w {a c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvc : v < c) (hcw : c < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hac : a < c := lt_trans hav hvc
  have haw : a < w := lt_trans hac hcw
  have huc : u < c := lt_trans hua hac
  have hu0 : u < 0 := lt_trans hua (lt_trans haw hw0)
  have hv0 : v < 0 := lt_trans hvc (lt_trans hcw hw0)
  have hc0 : c < 0 := lt_trans hcw hw0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hsq_pos : 0 < (u - a) * (u - a) :=
      mul_pos_of_neg_of_neg hua_neg hua_neg
    have hprod_neg : (u - a) * (u - a) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - a) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have htail_pos : 0 < (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg hav_neg haw_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - w)) :=
      mul_pos hau_pos htail_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
    have hprod_neg : (v - a) * (v - a) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - a) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have hhead_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
    have hprod_pos : 0 < (w - a) * (w - a) * (w - c) :=
      mul_pos hsq_pos hwc_pos
    have hleft_neg : w * ((w - a) * (w - a) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a a c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a a c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hav hcw (le_refl a) (le_of_lt hvc) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_a_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-upper-endpoint package for the repeated lower left root `a = b`.
Common-root endpoint coincidences are factored out; the remaining two orders use
the adjacent-interval sign-change lemmas above. -/
lemma xSubCubicCubicSplits_of_lower_left_double_root {a c u v w μ : ℝ}
    (hac : a < c) (huv : u ≤ v) (hvw : v ≤ w)
    (hua : u ≤ a) (hvc : v ≤ c) (hav : a ≤ v) (haw : a ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_of_lt hac) hvw hvc haw hc0 (le_of_lt hw0) hμ
  by_cases hva_eq : v = a
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_refl a) (le_of_lt hac) hua haw hc0 (le_of_lt hw0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have huw : u ≤ w := huv.trans hvw
    have ha0 : a ≤ 0 := (le_of_lt hac).trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := c) (a := a) (b := a) (c := u) (d := w)
      (le_refl a) huw haw hua ha0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc_eq : w = c
  · subst w
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_refl a) (le_of_lt hac) huv hua hav hvc hc0 hμ
  have hua_lt : u < a := lt_of_le_of_ne hua hua_eq
  have hav_lt : a < v := lt_of_le_of_ne hav (by intro h; exact hva_eq h.symm)
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  by_cases hwc : w < c
  · exact xSubCubicCubicSplits_of_order_u_a_a_v_w_c
      hua_lt hav_lt hvw hwc hc0 hμ
  · have hcw : c < w :=
      lt_of_le_of_ne (le_of_not_gt hwc) (by intro h; exact hwc_eq h.symm)
    exact xSubCubicCubicSplits_of_order_u_a_a_v_c_w
      hua_lt hav_lt hvc_lt hcw hw0 hμ

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a < v < b = c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_v_b_b_w {a b u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvb : v < b) (hbw : b < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hav hvb
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_trans hua hab
  have hu0 : u < 0 := lt_trans hua (lt_trans haw hw0)
  have hv0 : v < 0 := lt_trans hvb (lt_trans hbw hw0)
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have hsq_pos : 0 < (u - b) * (u - b) :=
      mul_pos_of_neg_of_neg hub_neg hub_neg
    have hprod_neg : (u - a) * ((u - b) * (u - b)) < 0 :=
      mul_neg_of_neg_of_pos hua_neg hsq_pos
    have hleft_pos : 0 < u * ((u - a) * ((u - b) * (u - b))) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have htail_pos : 0 < (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg hav_neg haw_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - w)) :=
      mul_pos hau_pos htail_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hsq_pos : 0 < (v - b) * (v - b) :=
      mul_pos_of_neg_of_neg hvb_neg hvb_neg
    have hprod_pos : 0 < (v - a) * ((v - b) * (v - b)) :=
      mul_pos hva_pos hsq_pos
    have hleft_neg : v * ((v - a) * ((v - b) * (v - b))) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hhead_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hsq_pos : 0 < (w - b) * (w - b) := mul_pos hwb_pos hwb_pos
    have hprod_pos : 0 < (w - a) * ((w - b) * (w - b)) :=
      mul_pos hwa_pos hsq_pos
    have hleft_neg : w * ((w - a) * ((w - b) * (w - b))) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b b u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b b u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hvb hbw (le_of_lt hav) (le_refl b) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u ≤ v < b = c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_v_b_b_w {a b u v w μ : ℝ}
    (hau : a < u) (huv : u ≤ v) (hvb : v < b) (hbw : b < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hav : a < v := lt_of_lt_of_le hau huv
  have hab : a < b := lt_trans hav hvb
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_of_le_of_lt huv hvb
  have hu0 : u < 0 := lt_trans hub (lt_trans hbw hw0)
  have hv0 : v < 0 := lt_trans hvb (lt_trans hbw hw0)
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hhead_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have hsq_pos : 0 < (u - b) * (u - b) :=
      mul_pos_of_neg_of_neg hub_neg hub_neg
    have hprod_pos : 0 < (u - a) * ((u - b) * (u - b)) :=
      mul_pos hua_pos hsq_pos
    have hleft_neg : u * ((u - a) * ((u - b) * (u - b))) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hsq_pos : 0 < (v - b) * (v - b) :=
      mul_pos_of_neg_of_neg hvb_neg hvb_neg
    have hprod_pos : 0 < (v - a) * ((v - b) * (v - b)) :=
      mul_pos hva_pos hsq_pos
    have hleft_neg : v * ((v - a) * ((v - b) * (v - b))) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hhead_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hsq_pos : 0 < (w - b) * (w - b) := mul_pos hwb_pos hwb_pos
    have hprod_pos : 0 < (w - a) * ((w - b) * (w - b)) :=
      mul_pos hwa_pos hsq_pos
    have hleft_neg : w * ((w - a) * ((w - b) * (w - b))) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b b u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b b u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hvb hbw huv (le_refl b) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-upper-endpoint package for the repeated upper left root `b = c`.
Common-root endpoint coincidences are factored out; the remaining two orders use
the adjacent-interval sign-change lemmas above. -/
lemma xSubCubicCubicSplits_of_upper_left_double_root {a b u v w μ : ℝ}
    (hab : a < b) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ b) (hvb : v ≤ b) (hav : a ≤ v) (hbw : b ≤ w)
    (hb0 : b < 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_refl b) hvw hvb hbw (le_of_lt hb0) (le_of_lt hw0) hμ
  by_cases hva_eq : v = a
  · subst v
    have huw : u ≤ w := huv.trans hvw
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := a) (a := b) (b := b) (c := u) (d := w)
      (le_refl b) huw hbw hub (le_of_lt hb0) (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hvb_eq : v = b
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_refl b) hub hbw (le_of_lt hb0) (le_of_lt hw0) hμ
  by_cases hwb_eq : w = b
  · subst w
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_refl b) huv hub hav hvb (le_of_lt hb0) hμ
  have hav_lt : a < v := lt_of_le_of_ne hav (by intro h; exact hva_eq h.symm)
  have hvb_lt : v < b := lt_of_le_of_ne hvb hvb_eq
  have hbw_lt : b < w := lt_of_le_of_ne hbw (by intro h; exact hwb_eq h.symm)
  by_cases hua : u < a
  · exact xSubCubicCubicSplits_of_order_u_a_v_b_b_w
      hua hav_lt hvb_lt hbw_lt hw0 hμ
  · have hau : a < u :=
      lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
    exact xSubCubicCubicSplits_of_order_a_u_v_b_b_w
      hau huv hvb_lt hbw_lt hw0 hμ

/-- Boundary case where both upper endpoint roots are zero.  Factoring out
`X` reduces the cubic/cubic leaf to the proved quadratic/quadratic leaf. -/
lemma xSubCubicCubicSplits_of_upper_roots_zero {a b u v μ : ℝ}
    (hab : a ≤ b) (huv : u ≤ v) (hav : a ≤ v) (hub : u ≤ b)
    (hb0 : b ≤ 0) (hv0 : v ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * X) -
      C μ * ((X - C u) * (X - C v) * X)).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C b)) -
    C μ * ((X - C u) * (X - C v))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact xSubQuadraticQuadraticSplits hab huv hav hub hb0 hv0 hμ
  have hfactor :
      X * ((X - C a) * (X - C b) * X) -
        C μ * ((X - C u) * (X - C v) * X) = X * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hQ

/-- Boundary case where the upper right root is zero.  Factoring out `X`
reduces the cubic/cubic leaf to the cubic-minus-quadratic pencil above. -/
lemma xSubCubicCubicSplits_of_right_upper_root_zero {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * X)).Splits := by
  let Q : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact cubicSubQuadratic_splits_of_roots_le hab hbc huv hub hvc hav hμ
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v) * X) = X * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hQ

/-- Normalized cubic/cubic leaf with weak left-root order, nonpositive upper
left endpoint, and strictly negative upper right endpoint.  This dispatcher
packages the strict-left-root case, the two left repeated-root boundaries, and
the triple-left-root common-root boundary. -/
lemma xSubCubicCubicSplits_of_negative_endpoints {a b c u v w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hab_eq : a = b
  · subst b
    by_cases hac_eq : a = c
    · subst c
      have hvc_eq : v = a := le_antisymm hvc hav
      subst v
      exact xSubCubicCubicSplits_of_middle_common_root
        (le_refl a) (le_refl a) hub hbw hc0 (le_of_lt hw0) hμ
    · have hac_lt : a < c := lt_of_le_of_ne hbc hac_eq
      exact xSubCubicCubicSplits_of_lower_left_double_root
        hac_lt huv hvw hub hvc hav hbw hc0 hw0 hμ
  by_cases hbc_eq : b = c
  · subst c
    have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
    have hb0 : b < 0 := lt_of_le_of_lt hbw hw0
    exact xSubCubicCubicSplits_of_upper_left_double_root
      hab_lt huv hvw hub hvc hav hbw hb0 hw0 hμ
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  exact xSubCubicCubicSplits_of_strict_left_roots
    hab_lt hbc_lt huv hvw hub hvc hav hbw hc0 hw0 hμ

/-- The normalized monic cubic/cubic x-subtraction leaf. -/
theorem xSubCubicCubicSplits :
    xSubCubicCubicSplitsStatement := by
  intro a b c u v w μ hab hbc huv hvw hub hvc hav hbw hc0 hw0 hμ
  by_cases hw_eq : w = 0
  · subst w
    by_cases hc_eq : c = 0
    · subst c
      simpa using xSubCubicCubicSplits_of_upper_roots_zero
        hab huv hav hub hbw hvc hμ
    · simpa using xSubCubicCubicSplits_of_right_upper_root_zero
        hab hbc huv hub hvc hav hμ
  · have hw_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
    exact xSubCubicCubicSplits_of_negative_endpoints
      hab hbc huv hvw hub hvc hav hbw hc0 hw_lt hμ

/-- The normalized monic cubic/cubic x-subtraction leaf implies the
degree-three/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, c, u, v, w, hab, hbc, huv, hvw, hproots, hqroots,
      hpfac, hqfac, hub, hvc, hav, hbw⟩ :=
    exists_roots_order_of_positiveSplitRootCountPair_three_three
      hpair hpdeg hqdeg
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn c hc_mem
  have hw0 : w ≤ 0 := by
    have hw_mem : w ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn w hw_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C ν * ((X - C u) * (X - C v) * (X - C w))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hbc huv hvw hub hvc hav hbw hc0 hw0 hν_pos
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfac, hqfac]
    dsimp [inner, ν, A, B]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hpair.left_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- The normalized monic cubic/cubic x-subtraction leaf implies the
degree-three/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    xSubCubicCubicSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-three right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 3 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 3 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 3 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Degree-three right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree three for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_two : g.natDegree ≤ 2
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
      hpair hfnn hgnn hdeg hle_two
  · have hthree : g.natDegree = 3 := by
      lia
    exact
      positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
        hmono hpair hfnn hgnn hdeg hthree

/-- Endpoint cases through right degree three for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits

/-- Pack the endpoint cases through degree three as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree three as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits

/-- Choosing the tangent slope at a right-outside point gives a monic
cubic-minus-linear pencil with negative discriminant. -/
lemma cubicDiscr_cubicSubLinear_slope_right_neg
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) :
    let μ : ℝ :=
      (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 := by
  intro μ
  have hdisc_eq :
      cubicDiscr
          (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) =
        -((u - c) * (u - b) * (u - a) *
          (4 * (b - a) ^ 3 + 24 * (b - a) ^ 2 * (c - b) +
            36 * (b - a) ^ 2 * (u - c) +
            48 * (b - a) * (c - b) ^ 2 +
            171 * (b - a) * (c - b) * (u - c) +
            135 * (b - a) * (u - c) ^ 2 + 32 * (c - b) ^ 3 +
            171 * (c - b) ^ 2 * (u - c) +
            270 * (c - b) * (u - c) ^ 2 +
            135 * (u - c) ^ 3)) := by
    rw [cubicSubLinear_eq_cubic_expansion, cubicDiscr_of_coeffs]
    dsimp [μ]
    ring_nf
  rw [hdisc_eq]
  have huc : 0 < u - c := sub_pos.mpr hcu
  have hub : 0 < u - b := sub_pos.mpr (lt_of_le_of_lt hbc hcu)
  have hua : 0 < u - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcu)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
  have hbracket :
      0 < 4 * (b - a) ^ 3 + 24 * (b - a) ^ 2 * (c - b) +
        36 * (b - a) ^ 2 * (u - c) +
        48 * (b - a) * (c - b) ^ 2 +
        171 * (b - a) * (c - b) * (u - c) +
        135 * (b - a) * (u - c) ^ 2 + 32 * (c - b) ^ 3 +
        171 * (c - b) ^ 2 * (u - c) +
        270 * (c - b) * (u - c) ^ 2 +
        135 * (u - c) ^ 3 := by
    positivity
  nlinarith [mul_pos (mul_pos (mul_pos huc hub) hua) hbracket]

/-- Choosing the tangent slope at a left-outside point gives a monic
cubic-minus-linear pencil with negative discriminant. -/
lemma cubicDiscr_cubicSubLinear_slope_left_neg
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    let μ : ℝ :=
      (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 := by
  intro μ
  have hdisc_eq :
      cubicDiscr
          (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) =
        -((a - u) * (b - u) * (c - u) *
          (135 * (a - u) ^ 3 + 270 * (a - u) ^ 2 * (b - a) +
            135 * (a - u) ^ 2 * (c - b) +
            171 * (a - u) * (b - a) ^ 2 +
            171 * (a - u) * (b - a) * (c - b) +
            36 * (a - u) * (c - b) ^ 2 + 32 * (b - a) ^ 3 +
            48 * (b - a) ^ 2 * (c - b) +
            24 * (b - a) * (c - b) ^ 2 + 4 * (c - b) ^ 3)) := by
    rw [cubicSubLinear_eq_cubic_expansion, cubicDiscr_of_coeffs]
    dsimp [μ]
    ring_nf
  rw [hdisc_eq]
  have hau : 0 < a - u := sub_pos.mpr hua
  have hbu : 0 < b - u := sub_pos.mpr (lt_of_lt_of_le hua hab)
  have hcu : 0 < c - u := sub_pos.mpr (lt_of_lt_of_le hua (hab.trans hbc))
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
  have hbracket :
      0 < 135 * (a - u) ^ 3 + 270 * (a - u) ^ 2 * (b - a) +
        135 * (a - u) ^ 2 * (c - b) +
        171 * (a - u) * (b - a) ^ 2 +
        171 * (a - u) * (b - a) * (c - b) +
        36 * (a - u) * (c - b) ^ 2 + 32 * (b - a) ^ 3 +
        48 * (b - a) ^ 2 * (c - b) +
        24 * (b - a) * (c - b) ^ 2 + 4 * (c - b) ^ 3 := by
    positivity
  nlinarith [mul_pos (mul_pos (mul_pos hau hbu) hcu) hbracket]

/-- If the linear root lies strictly above the cubic roots, then some positive
subtraction coefficient makes the monic cubic-minus-linear pencil fail to
split. -/
lemma exists_cubicSubLinear_not_splits_of_upper_lt_right_root
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).Splits := by
  let μ : ℝ :=
    (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
  have hμ : 0 < μ := by
    dsimp [μ]
    have huc : 0 < u - c := sub_pos.mpr hcu
    have hub : 0 < u - b := sub_pos.mpr (lt_of_le_of_lt hbc hcu)
    have hua : 0 < u - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcu)
    positivity
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).natDegree ≤ 3 := by
    rw [natDegree_cubicSubLinear]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 :=
    cubicDiscr_cubicSubLinear_slope_right_neg hab hbc hcu
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- If the linear root lies strictly below the cubic roots, then some positive
subtraction coefficient makes the monic cubic-minus-linear pencil fail to
split. -/
lemma exists_cubicSubLinear_not_splits_of_left_root_lt_lower
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).Splits := by
  let μ : ℝ :=
    (u - b) * (u - c) + (u - a) * (u - c) + (u - a) * (u - b)
  have hμ : 0 < μ := by
    dsimp [μ]
    have hba : u - b < 0 := sub_neg.mpr (lt_of_lt_of_le hua hab)
    have hca : u - c < 0 := sub_neg.mpr (lt_of_lt_of_le hua (hab.trans hbc))
    have hua' : u - a < 0 := sub_neg.mpr hua
    have h1 : 0 < (u - b) * (u - c) := mul_pos_of_neg_of_neg hba hca
    have h2 : 0 < (u - a) * (u - c) := mul_pos_of_neg_of_neg hua' hca
    have h3 : 0 < (u - a) * (u - b) := mul_pos_of_neg_of_neg hua' hba
    linarith
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).natDegree ≤ 3 := by
    rw [natDegree_cubicSubLinear]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) < 0 :=
    cubicDiscr_cubicSubLinear_slope_left_neg hab hbc hua
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- The midpoint tangent coefficient is positive when the average of the
quadratic roots lies strictly above the cubic root interval. -/
lemma cubicSubQuadratic_average_above_mu_pos {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcmean : c < (u + v) / 2) :
    0 < 3 * ((u + v) / 2) - (a + b + c) := by
  let m : ℝ := (u + v) / 2
  have hcm : c < m := by
    simpa [m] using hcmean
  have hma : 0 < m - a := by linarith
  have hmb : 0 < m - b := by linarith
  have hmc : 0 < m - c := by linarith
  have hsum :
      3 * m - (a + b + c) = (m - a) + (m - b) + (m - c) := by
    ring
  change 0 < 3 * m - (a + b + c)
  rw [hsum]
  nlinarith

/-- With the midpoint tangent coefficient, the derivative discriminant of the
cubic-minus-quadratic pencil is negative when the average of the quadratic
roots lies strictly above the cubic root interval. -/
lemma cubicSubQuadratic_average_above_deriv_disc_neg {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcmean : c < (u + v) / 2) :
    (-(a + b + c + (3 * ((u + v) / 2) - (a + b + c)))) ^ 2 <
      3 * 1 *
        (a * b + a * c + b * c +
          (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) := by
  let m : ℝ := (u + v) / 2
  have hcm : c < m := by
    simpa [m] using hcmean
  have hma : 0 < m - a := by linarith
  have hmb : 0 < m - b := by linarith
  have hmc : 0 < m - c := by linarith
  have hp1 : 0 < (m - a) * (m - b) := mul_pos hma hmb
  have hp2 : 0 < (m - a) * (m - c) := mul_pos hma hmc
  have hp3 : 0 < (m - b) * (m - c) := mul_pos hmb hmc
  have hsum_pos :
      0 < (m - a) * (m - b) + (m - a) * (m - c) +
        (m - b) * (m - c) := by
    nlinarith
  have hdelta :
      3 * 1 *
          (a * b + a * c + b * c +
            (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) -
          (-(a + b + c + (3 * ((u + v) / 2) - (a + b + c)))) ^ 2 =
        3 * ((m - a) * (m - b) + (m - a) * (m - c) +
          (m - b) * (m - c)) := by
    dsimp [m]
    ring
  nlinarith

/-- If the average of the quadratic roots lies strictly above the cubic root
interval, then the midpoint tangent coefficient gives a negative cubic
discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_average_above_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcmean : c < (u + v) / 2) :
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C (3 * ((u + v) / 2) - (a + b + c)) *
          ((X - C u) * (X - C v))) < 0 := by
  rw [cubicSubQuadratic_eq_cubic_expansion]
  exact
    cubicDiscr_neg_of_deriv_disc_neg
      1
      (-(a + b + c + (3 * ((u + v) / 2) - (a + b + c))))
      (a * b + a * c + b * c +
        (3 * ((u + v) / 2) - (a + b + c)) * (u + v))
      (-(a * b * c) -
        (3 * ((u + v) / 2) - (a + b + c)) * (u * v))
      (by norm_num)
      (cubicSubQuadratic_average_above_deriv_disc_neg hab hbc hcmean)

/-- If the average of the quadratic roots lies strictly above the cubic root
interval, then some positive subtraction coefficient makes the monic
cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_average_above
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcmean : c < (u + v) / 2) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  let μ : ℝ := 3 * ((u + v) / 2) - (a + b + c)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_average_above_mu_pos hab hbc hcmean
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).natDegree ≤ 3 := by
    rw [natDegree_cubicSubQuadratic]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_average_above_neg hab hbc hcmean
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- The midpoint tangent coefficient is positive when both quadratic roots lie
strictly above the cubic root interval. -/
lemma cubicSubQuadratic_right_roots_above_mu_pos {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) (huv : u ≤ v) :
    0 < 3 * ((u + v) / 2) - (a + b + c) := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact cubicSubQuadratic_average_above_mu_pos hab hbc hcmean

/-- With the midpoint tangent coefficient, the derivative discriminant of the
cubic-minus-quadratic pencil is negative. -/
lemma cubicSubQuadratic_right_roots_above_deriv_disc_neg {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) (huv : u ≤ v) :
    (-(a + b + c + (3 * ((u + v) / 2) - (a + b + c)))) ^ 2 <
      3 * 1 *
        (a * b + a * c + b * c +
          (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact cubicSubQuadratic_average_above_deriv_disc_neg hab hbc hcmean

/-- If both quadratic roots lie strictly above the cubic roots, then the
midpoint tangent coefficient gives a negative cubic discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_right_roots_above_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u)
    (huv : u ≤ v) :
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C (3 * ((u + v) / 2) - (a + b + c)) *
          ((X - C u) * (X - C v))) < 0 := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact cubicDiscr_cubicSubQuadratic_average_above_neg hab hbc hcmean

/-- If both quadratic roots lie strictly above the cubic roots, then some
positive subtraction coefficient makes the monic cubic-minus-quadratic pencil
fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_right_roots_above
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u)
    (huv : u ≤ v) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact exists_cubicSubQuadratic_not_splits_of_average_above hab hbc hcmean

/-- Tangent-at-`v` coefficient for the right-protruding branch where the lower
quadratic root lies weakly below the cubic root interval. -/
lemma cubicSubQuadratic_right_protruding_left_below_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u ≤ a)
    (hcv : c < v) :
    0 <
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u) := by
  have hvb_pos : 0 < v - b := sub_pos.mpr (lt_of_le_of_lt hbc hcv)
  have hvc_pos : 0 < v - c := sub_pos.mpr hcv
  have hva_pos : 0 < v - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcv)
  have hvu_pos : 0 < v - u :=
    sub_pos.mpr (lt_of_le_of_lt (hua.trans (hab.trans hbc)) hcv)
  have hnum :
      0 < (v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b) := by
    positivity
  exact div_pos hnum hvu_pos

private def cubicSubQuadraticRightProtrudingLeftBelowBracket
    (sau dab dbc dcv : ℝ) : ℝ :=
  4 * dab ^ 6 + 24 * dab ^ 5 * dbc + 24 * dab ^ 5 * dcv +
    12 * dab ^ 5 * sau + 60 * dab ^ 4 * dbc ^ 2 +
    135 * dab ^ 4 * dbc * dcv + 72 * dab ^ 4 * dbc * sau +
    75 * dab ^ 4 * dcv ^ 2 + 84 * dab ^ 4 * dcv * sau +
    12 * dab ^ 4 * sau ^ 2 + 80 * dab ^ 3 * dbc ^ 3 +
    300 * dab ^ 3 * dbc ^ 2 * dcv +
    168 * dab ^ 3 * dbc ^ 2 * sau +
    360 * dab ^ 3 * dbc * dcv ^ 2 +
    441 * dab ^ 3 * dbc * dcv * sau +
    72 * dab ^ 3 * dbc * sau ^ 2 + 140 * dab ^ 3 * dcv ^ 3 +
    273 * dab ^ 3 * dcv ^ 2 * sau +
    96 * dab ^ 3 * dcv * sau ^ 2 + 4 * dab ^ 3 * sau ^ 3 +
    60 * dab ^ 2 * dbc ^ 4 + 330 * dab ^ 2 * dbc ^ 3 * dcv +
    192 * dab ^ 2 * dbc ^ 3 * sau +
    642 * dab ^ 2 * dbc ^ 2 * dcv ^ 2 +
    795 * dab ^ 2 * dbc ^ 2 * dcv * sau +
    156 * dab ^ 2 * dbc ^ 2 * sau ^ 2 +
    534 * dab ^ 2 * dbc * dcv ^ 3 +
    990 * dab ^ 2 * dbc * dcv ^ 2 * sau +
    477 * dab ^ 2 * dbc * dcv * sau ^ 2 +
    24 * dab ^ 2 * dbc * sau ^ 3 + 162 * dab ^ 2 * dcv ^ 4 +
    387 * dab ^ 2 * dcv ^ 3 * sau +
    333 * dab ^ 2 * dcv ^ 2 * sau ^ 2 +
    36 * dab ^ 2 * dcv * sau ^ 3 + 24 * dab * dbc ^ 5 +
    180 * dab * dbc ^ 4 * dcv + 108 * dab * dbc ^ 4 * sau +
    504 * dab * dbc ^ 3 * dcv ^ 2 +
    603 * dab * dbc ^ 3 * dcv * sau +
    144 * dab * dbc ^ 3 * sau ^ 2 +
    672 * dab * dbc ^ 2 * dcv ^ 3 +
    1125 * dab * dbc ^ 2 * dcv ^ 2 * sau +
    666 * dab * dbc ^ 2 * dcv * sau ^ 2 +
    48 * dab * dbc ^ 2 * sau ^ 3 + 432 * dab * dbc * dcv ^ 4 +
    873 * dab * dbc * dcv ^ 3 * sau +
    900 * dab * dbc * dcv ^ 2 * sau ^ 2 +
    171 * dab * dbc * dcv * sau ^ 3 + 108 * dab * dcv ^ 5 +
    243 * dab * dcv ^ 4 * sau + 378 * dab * dcv ^ 3 * sau ^ 2 +
    135 * dab * dcv ^ 2 * sau ^ 3 + 4 * dbc ^ 6 +
    39 * dbc ^ 5 * dcv + 24 * dbc ^ 5 * sau +
    147 * dbc ^ 4 * dcv ^ 2 + 165 * dbc ^ 4 * dcv * sau +
    48 * dbc ^ 4 * sau ^ 2 + 274 * dbc ^ 3 * dcv ^ 3 +
    420 * dbc ^ 3 * dcv ^ 2 * sau +
    273 * dbc ^ 3 * dcv * sau ^ 2 + 32 * dbc ^ 3 * sau ^ 3 +
    270 * dbc ^ 2 * dcv ^ 4 + 522 * dbc ^ 2 * dcv ^ 3 * sau +
    495 * dbc ^ 2 * dcv ^ 2 * sau ^ 2 +
    171 * dbc ^ 2 * dcv * sau ^ 3 + 135 * dbc * dcv ^ 5 +
    324 * dbc * dcv ^ 4 * sau + 351 * dbc * dcv ^ 3 * sau ^ 2 +
    270 * dbc * dcv ^ 2 * sau ^ 3 + 27 * dcv ^ 6 +
    81 * dcv ^ 5 * sau + 81 * dcv ^ 4 * sau ^ 2 +
    135 * dcv ^ 3 * sau ^ 3

private lemma cubicSubQuadraticRightProtrudingLeftBelowBracket_pos
    {sau dab dbc dcv : ℝ} (hsau : 0 ≤ sau) (hdab : 0 ≤ dab)
    (hdbc : 0 ≤ dbc) (hdcv : 0 < dcv) :
    0 < cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv := by
  dsimp [cubicSubQuadraticRightProtrudingLeftBelowBracket]
  positivity

/-- Normalized gap-coordinate discriminant identity for the right-protruding
cubic/quadratic obstruction with lower quadratic root below the cubic interval.
-/
private lemma cubicDiscr_cubicSubQuadratic_right_protruding_left_below_norm
    (sau dab dbc dcv : ℝ) (hden_ne : sau + dab + dbc + dcv ≠ 0) :
    let μ : ℝ :=
      (dab * dbc + 2 * dab * dcv + dbc ^ 2 + 4 * dbc * dcv + 3 * dcv ^ 2) /
        (sau + dab + dbc + dcv)
    cubicDiscr
      (((X - C sau) * (X - C (sau + dab)) *
          (X - C (sau + dab + dbc))) -
        C μ * ((X - C 0) * (X - C (sau + dab + dbc + dcv)))) =
      -(dcv * (dbc + dcv) * (dab + dbc + dcv) *
        cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv /
          (sau + dab + dbc + dcv) ^ 3) := by
  intro μ
  have hpoly :
      ((X - C sau) * (X - C (sau + dab)) *
            (X - C (sau + dab + dbc)) -
          C μ * ((X - C 0) * (X - C (sau + dab + dbc + dcv)))) =
        C 1 * X ^ 3 +
          C (-(2 * dab ^ 2 + 4 * dab * dbc + 4 * dab * dcv +
              5 * dab * sau + 2 * dbc ^ 2 + 5 * dbc * dcv +
              4 * dbc * sau + 3 * dcv ^ 2 + 3 * dcv * sau +
              3 * sau ^ 2) / (sau + dab + dbc + dcv)) * X ^ 2 +
          C (dab ^ 2 + 2 * dab * dbc + 2 * dab * dcv + 4 * dab * sau +
              dbc ^ 2 + 4 * dbc * dcv + 2 * dbc * sau + 3 * dcv ^ 2 +
              3 * sau ^ 2) * X +
          C (-(sau * (dab + sau) * (dab + dbc + sau))) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    dsimp [μ]
    field_simp [hden_ne]
    ring_nf
  rw [hpoly, cubicDiscr_of_coeffs]
  dsimp [cubicSubQuadraticRightProtrudingLeftBelowBracket]
  field_simp [hden_ne]
  ring_nf

/-- If the upper quadratic root lies strictly above the cubic root interval and
the lower quadratic root lies weakly below the lower cubic root, then
tangent at the upper quadratic root gives a negative cubic discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_right_protruding_left_below_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u ≤ a)
    (hcv : c < v) :
    let μ : ℝ :=
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) < 0 := by
  intro μ
  let sau : ℝ := a - u
  let dab : ℝ := b - a
  let dbc : ℝ := c - b
  let dcv : ℝ := v - c
  have hden_pos : 0 < sau + dab + dbc + dcv := by
    dsimp [sau, dab, dbc, dcv]
    linarith
  have hden_ne : sau + dab + dbc + dcv ≠ 0 := ne_of_gt hden_pos
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hshift : cubicDiscr P = cubicDiscr (P.comp (X + C u)) := by
    dsimp [P]
    rw [cubicSubQuadratic_eq_cubic_expansion]
    exact
      (cubicDiscr_cubic_comp_X_add_C
        1 (-(a + b + c + μ))
        (a * b + a * c + b * c + μ * (u + v))
        (-(a * b * c) - μ * (u * v)) u).symm
  have hcomp_eq :
      P.comp (X + C u) =
        ((X - C sau) * (X - C (sau + dab)) *
            (X - C (sau + dab + dbc))) -
          C ((dab * dbc + 2 * dab * dcv + dbc ^ 2 + 4 * dbc * dcv +
              3 * dcv ^ 2) / (sau + dab + dbc + dcv)) *
            ((X - C 0) * (X - C (sau + dab + dbc + dcv))) := by
    dsimp [P]
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    dsimp [μ, sau, dab, dbc, dcv]
    field_simp [hden_ne]
    ring_nf
  have hdisc_eq :
      cubicDiscr P =
        -(dcv * (dbc + dcv) * (dab + dbc + dcv) *
          cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv /
            (sau + dab + dbc + dcv) ^ 3) := by
    rw [hshift, hcomp_eq]
    exact cubicDiscr_cubicSubQuadratic_right_protruding_left_below_norm
      sau dab dbc dcv hden_ne
  change cubicDiscr P < 0
  rw [hdisc_eq]
  have hsau_nonneg : 0 ≤ sau := by
    dsimp [sau]
    linarith
  have hdab_nonneg : 0 ≤ dab := by
    dsimp [dab]
    linarith
  have hdbc_nonneg : 0 ≤ dbc := by
    dsimp [dbc]
    linarith
  have hdcv_pos : 0 < dcv := by
    dsimp [dcv]
    linarith
  have hbracket :
      0 < cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv :=
    cubicSubQuadraticRightProtrudingLeftBelowBracket_pos
      hsau_nonneg hdab_nonneg hdbc_nonneg hdcv_pos
  have hnum :
      0 <
        dcv * (dbc + dcv) * (dab + dbc + dcv) *
          cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv := by
    positivity
  have hfrac :
      0 <
        dcv * (dbc + dcv) * (dab + dbc + dcv) *
          cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv /
            (sau + dab + dbc + dcv) ^ 3 :=
    div_pos hnum (by positivity)
  nlinarith

/-- In the right-protruding branch where the lower quadratic root lies weakly
below the cubic interval, some positive subtraction coefficient makes the
monic cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_right_protruding_left_below
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u ≤ a)
    (hcv : c < v) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  let μ : ℝ :=
    ((v - b) * (v - c) + (v - a) * (v - c) +
      (v - a) * (v - b)) / (v - u)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_right_protruding_left_below_mu_pos
      hab hbc hua hcv
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).natDegree ≤ 3 := by
    rw [natDegree_cubicSubQuadratic]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_right_protruding_left_below_neg
      hab hbc hua hcv
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- Tangent-at-`v` coefficient for the strict lower-side cubic/quadratic
obstruction. -/
lemma cubicSubQuadratic_left_roots_below_strict_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hva : v < a) :
    0 <
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u) := by
  have hva_neg : v - a < 0 := sub_neg.mpr hva
  have hvb_neg : v - b < 0 := sub_neg.mpr (lt_of_lt_of_le hva hab)
  have hvc_neg : v - c < 0 := sub_neg.mpr (lt_of_lt_of_le hva (hab.trans hbc))
  have h1 : 0 < (v - b) * (v - c) := mul_pos_of_neg_of_neg hvb_neg hvc_neg
  have h2 : 0 < (v - a) * (v - c) := mul_pos_of_neg_of_neg hva_neg hvc_neg
  have h3 : 0 < (v - a) * (v - b) := mul_pos_of_neg_of_neg hva_neg hvb_neg
  have hnum :
      0 < (v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b) := by
    linarith
  exact div_pos hnum (sub_pos.mpr huv)

private def cubicSubQuadraticLeftBelowStrictBracket
    (duv sav dab dbc : ℝ) : ℝ :=
  4 * dab ^ 6 + 12 * dab ^ 5 * dbc + 24 * dab ^ 5 * duv +
    48 * dab ^ 5 * sav + 12 * dab ^ 4 * dbc ^ 2 +
    60 * dab ^ 4 * dbc * duv + 120 * dab ^ 4 * dbc * sav +
    48 * dab ^ 4 * duv ^ 2 + 228 * dab ^ 4 * duv * sav +
    228 * dab ^ 4 * sav ^ 2 + 4 * dab ^ 3 * dbc ^ 3 +
    48 * dab ^ 3 * dbc ^ 2 * duv + 96 * dab ^ 3 * dbc ^ 2 * sav +
    96 * dab ^ 3 * dbc * duv ^ 2 + 456 * dab ^ 3 * dbc * duv * sav +
    456 * dab ^ 3 * dbc * sav ^ 2 + 32 * dab ^ 3 * duv ^ 3 +
    336 * dab ^ 3 * duv ^ 2 * sav + 816 * dab ^ 3 * duv * sav ^ 2 +
    544 * dab ^ 3 * sav ^ 3 + 12 * dab ^ 2 * dbc ^ 3 * duv +
    24 * dab ^ 2 * dbc ^ 3 * sav + 60 * dab ^ 2 * dbc ^ 2 * duv ^ 2 +
    276 * dab ^ 2 * dbc ^ 2 * duv * sav +
    276 * dab ^ 2 * dbc ^ 2 * sav ^ 2 + 48 * dab ^ 2 * dbc * duv ^ 3 +
    504 * dab ^ 2 * dbc * duv ^ 2 * sav +
    1224 * dab ^ 2 * dbc * duv * sav ^ 2 +
    816 * dab ^ 2 * dbc * sav ^ 3 + 171 * dab ^ 2 * duv ^ 3 * sav +
    828 * dab ^ 2 * duv ^ 2 * sav ^ 2 +
    1368 * dab ^ 2 * duv * sav ^ 3 + 684 * dab ^ 2 * sav ^ 4 +
    12 * dab * dbc ^ 3 * duv ^ 2 + 48 * dab * dbc ^ 3 * duv * sav +
    48 * dab * dbc ^ 3 * sav ^ 2 + 24 * dab * dbc ^ 2 * duv ^ 3 +
    216 * dab * dbc ^ 2 * duv ^ 2 * sav +
    504 * dab * dbc ^ 2 * duv * sav ^ 2 +
    336 * dab * dbc ^ 2 * sav ^ 3 + 171 * dab * dbc * duv ^ 3 * sav +
    828 * dab * dbc * duv ^ 2 * sav ^ 2 +
    1368 * dab * dbc * duv * sav ^ 3 + 684 * dab * dbc * sav ^ 4 +
    270 * dab * duv ^ 3 * sav ^ 2 + 864 * dab * duv ^ 2 * sav ^ 3 +
    1080 * dab * duv * sav ^ 4 + 432 * dab * sav ^ 5 +
    4 * dbc ^ 3 * duv ^ 3 + 24 * dbc ^ 3 * duv ^ 2 * sav +
    48 * dbc ^ 3 * duv * sav ^ 2 + 32 * dbc ^ 3 * sav ^ 3 +
    36 * dbc ^ 2 * duv ^ 3 * sav +
    180 * dbc ^ 2 * duv ^ 2 * sav ^ 2 +
    288 * dbc ^ 2 * duv * sav ^ 3 + 144 * dbc ^ 2 * sav ^ 4 +
    135 * dbc * duv ^ 3 * sav ^ 2 + 432 * dbc * duv ^ 2 * sav ^ 3 +
    540 * dbc * duv * sav ^ 4 + 216 * dbc * sav ^ 5 +
    135 * duv ^ 3 * sav ^ 3 + 324 * duv ^ 2 * sav ^ 4 +
    324 * duv * sav ^ 5 + 108 * sav ^ 6

private lemma cubicSubQuadraticLeftBelowStrictBracket_pos
    {duv sav dab dbc : ℝ} (hduv : 0 < duv) (hsav : 0 < sav)
    (hdab : 0 ≤ dab) (hdbc : 0 ≤ dbc) :
    0 < cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc := by
  dsimp [cubicSubQuadraticLeftBelowStrictBracket]
  positivity

/-- Normalized gap-coordinate discriminant identity for the strict lower-side
cubic/quadratic obstruction. -/
private lemma cubicDiscr_cubicSubQuadratic_left_roots_below_strict_norm
    (duv sav dab dbc : ℝ) (hduv_ne : duv ≠ 0) :
    let μ : ℝ :=
      (dab ^ 2 + dab * dbc + 4 * dab * sav + 2 * dbc * sav +
        3 * sav ^ 2) / duv
    cubicDiscr
      (((X - C (duv + sav)) * (X - C (duv + sav + dab)) *
          (X - C (duv + sav + dab + dbc))) -
        C μ * ((X - C 0) * (X - C duv))) =
      -(sav * (dab + sav) * (dab + dbc + sav) *
        cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc / duv ^ 3) := by
  intro μ
  have hpoly :
      ((X - C (duv + sav)) * (X - C (duv + sav + dab)) *
            (X - C (duv + sav + dab + dbc)) -
          C μ * ((X - C 0) * (X - C duv))) =
        C 1 * X ^ 3 +
          C ((-(dab ^ 2) - dab * dbc - 2 * dab * duv - 4 * dab * sav -
              dbc * duv - 2 * dbc * sav - 3 * duv ^ 2 - 3 * duv * sav -
              3 * sav ^ 2) / duv) * X ^ 2 +
          C (2 * dab ^ 2 + 2 * dab * dbc + 4 * dab * duv + 8 * dab * sav +
              2 * dbc * duv + 4 * dbc * sav + 3 * duv ^ 2 + 6 * duv * sav +
              6 * sav ^ 2) * X +
          C (-(dab ^ 2 * duv) - dab ^ 2 * sav - dab * dbc * duv -
              dab * dbc * sav - 2 * dab * duv ^ 2 - 4 * dab * duv * sav -
              2 * dab * sav ^ 2 - dbc * duv ^ 2 - 2 * dbc * duv * sav -
              dbc * sav ^ 2 - duv ^ 3 - 3 * duv ^ 2 * sav -
              3 * duv * sav ^ 2 - sav ^ 3) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    dsimp [μ]
    field_simp [hduv_ne]
    ring_nf
  rw [hpoly, cubicDiscr_of_coeffs]
  dsimp [cubicSubQuadraticLeftBelowStrictBracket]
  field_simp [hduv_ne]
  ring_nf

/-- If the two quadratic roots are strictly below the cubic root interval and
distinct, tangent at the upper quadratic root gives a negative cubic
discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_left_roots_below_strict_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hva : v < a) :
    let μ : ℝ :=
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) < 0 := by
  intro μ
  let duv : ℝ := v - u
  let sav : ℝ := a - v
  let dab : ℝ := b - a
  let dbc : ℝ := c - b
  have hduv_ne : duv ≠ 0 := ne_of_gt (by dsimp [duv]; linarith)
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hshift : cubicDiscr P = cubicDiscr (P.comp (X + C u)) := by
    dsimp [P]
    rw [cubicSubQuadratic_eq_cubic_expansion]
    exact
      (cubicDiscr_cubic_comp_X_add_C
        1 (-(a + b + c + μ))
        (a * b + a * c + b * c + μ * (u + v))
        (-(a * b * c) - μ * (u * v)) u).symm
  have hcomp_eq :
      P.comp (X + C u) =
        ((X - C (duv + sav)) * (X - C (duv + sav + dab)) *
            (X - C (duv + sav + dab + dbc))) -
          C ((dab ^ 2 + dab * dbc + 4 * dab * sav + 2 * dbc * sav +
              3 * sav ^ 2) / duv) * ((X - C 0) * (X - C duv)) := by
    dsimp [P]
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    dsimp [μ, duv, sav, dab, dbc]
    field_simp [hduv_ne]
    ring_nf
  have hdisc_eq :
      cubicDiscr P =
        -(sav * (dab + sav) * (dab + dbc + sav) *
          cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc / duv ^ 3) := by
    rw [hshift, hcomp_eq]
    exact cubicDiscr_cubicSubQuadratic_left_roots_below_strict_norm
      duv sav dab dbc hduv_ne
  change cubicDiscr P < 0
  rw [hdisc_eq]
  have hduv_pos : 0 < duv := by
    dsimp [duv]
    linarith
  have hsav_pos : 0 < sav := by
    dsimp [sav]
    linarith
  have hdab_nonneg : 0 ≤ dab := by
    dsimp [dab]
    linarith
  have hdbc_nonneg : 0 ≤ dbc := by
    dsimp [dbc]
    linarith
  have hbracket : 0 < cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc :=
    cubicSubQuadraticLeftBelowStrictBracket_pos hduv_pos hsav_pos
      hdab_nonneg hdbc_nonneg
  have hnum :
      0 <
        sav * (dab + sav) * (dab + dbc + sav) *
          cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc := by
    positivity
  have hfrac :
      0 <
        sav * (dab + sav) * (dab + dbc + sav) *
          cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc / duv ^ 3 :=
    div_pos hnum (by positivity)
  nlinarith

/-- If the two distinct quadratic roots lie strictly below the cubic roots, then
some positive subtraction coefficient makes the monic cubic-minus-quadratic
pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_left_roots_below_strict
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hva : v < a) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  let μ : ℝ :=
    ((v - b) * (v - c) + (v - a) * (v - c) +
      (v - a) * (v - b)) / (v - u)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_left_roots_below_strict_mu_pos hab hbc huv hva
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).natDegree ≤ 3 := by
    rw [natDegree_cubicSubQuadratic]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_left_roots_below_strict_neg
      hab hbc huv hva
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- Tangent coefficient for the lower-side cubic/quadratic obstruction when
the quadratic has a double root. -/
lemma cubicSubQuadratic_left_double_roots_below_mu_pos
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    0 < (b - u) * (c - u) / (a - u) := by
  have hau : 0 < a - u := sub_pos.mpr hua
  have hbu : 0 < b - u := sub_pos.mpr (lt_of_lt_of_le hua hab)
  have hcu : 0 < c - u := sub_pos.mpr (lt_of_lt_of_le hua (hab.trans hbc))
  exact div_pos (mul_pos hbu hcu) hau

private def cubicSubQuadraticLeftDoubleBelowBracket
    (sav dab dbc : ℝ) : ℝ :=
  3 * dab ^ 8 + 31 * sav ^ 8 + 3 * dab ^ 4 * dbc ^ 4 +
    12 * dab ^ 7 * dbc + 12 * dab ^ 5 * dbc ^ 3 +
    16 * dbc ^ 4 * sav ^ 4 + 18 * dab ^ 6 * dbc ^ 2 +
    40 * dab ^ 7 * sav + 72 * dbc ^ 3 * sav ^ 5 +
    106 * dbc * sav ^ 7 + 131 * dbc ^ 2 * sav ^ 6 +
    212 * dab * sav ^ 7 + 216 * dab ^ 6 * sav ^ 2 +
    612 * dab ^ 5 * sav ^ 3 + 624 * dab ^ 2 * sav ^ 6 +
    1014 * dab ^ 4 * sav ^ 4 + 1024 * dab ^ 3 * sav ^ 5 +
    20 * dab ^ 3 * dbc ^ 4 * sav + 48 * dab * dbc ^ 4 * sav ^ 3 +
    48 * dab ^ 2 * dbc ^ 4 * sav ^ 2 +
    100 * dab ^ 4 * dbc ^ 3 * sav + 140 * dab ^ 6 * dbc * sav +
    180 * dab ^ 5 * dbc ^ 2 * sav + 296 * dab * dbc ^ 3 * sav ^ 4 +
    312 * dab ^ 3 * dbc ^ 3 * sav ^ 2 +
    450 * dab ^ 2 * dbc ^ 3 * sav ^ 3 +
    624 * dab * dbc * sav ^ 6 + 648 * dab ^ 5 * dbc * sav ^ 2 +
    656 * dab * dbc ^ 2 * sav ^ 5 +
    696 * dab ^ 4 * dbc ^ 2 * sav ^ 2 +
    1310 * dab ^ 2 * dbc ^ 2 * sav ^ 4 +
    1320 * dab ^ 3 * dbc ^ 2 * sav ^ 3 +
    1530 * dab ^ 4 * dbc * sav ^ 3 +
    1536 * dab ^ 2 * dbc * sav ^ 5 +
    2028 * dab ^ 3 * dbc * sav ^ 4

private lemma cubicSubQuadraticLeftDoubleBelowBracket_pos
    {sav dab dbc : ℝ} (hsav : 0 < sav) (hdab : 0 ≤ dab) (hdbc : 0 ≤ dbc) :
    0 < cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc := by
  dsimp [cubicSubQuadraticLeftDoubleBelowBracket]
  positivity

/-- Normalized gap-coordinate discriminant identity for the lower-side
cubic/quadratic obstruction with a double quadratic root. -/
private lemma cubicDiscr_cubicSubQuadratic_left_double_roots_below_norm
    (sav dab dbc : ℝ) (hsav_ne : sav ≠ 0) :
    let μ : ℝ := (sav + dab) * (sav + dab + dbc) / sav
    cubicDiscr
      (((X - C sav) * (X - C (sav + dab)) *
          (X - C (sav + dab + dbc))) -
        C μ * ((X - C 0) * (X - C 0))) =
      -(cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc / sav ^ 2) := by
  intro μ
  have hpoly :
      ((X - C sav) * (X - C (sav + dab)) *
            (X - C (sav + dab + dbc)) -
          C μ * ((X - C 0) * (X - C 0))) =
        C 1 * X ^ 3 +
          C ((-(dab ^ 2) - dab * dbc - 4 * dab * sav -
              2 * dbc * sav - 4 * sav ^ 2) / sav) * X ^ 2 +
          C (dab ^ 2 + dab * dbc + 4 * dab * sav + 2 * dbc * sav +
              3 * sav ^ 2) * X +
          C (-(dab ^ 2 * sav) - dab * dbc * sav - 2 * dab * sav ^ 2 -
              dbc * sav ^ 2 - sav ^ 3) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    dsimp [μ]
    field_simp [hsav_ne]
    ring_nf
  rw [hpoly, cubicDiscr_of_coeffs]
  dsimp [cubicSubQuadraticLeftDoubleBelowBracket]
  field_simp [hsav_ne]
  ring_nf

/-- If the quadratic has a double root strictly below the cubic root interval,
then the tangent coefficient gives a negative cubic discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_left_double_roots_below_neg
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    let μ : ℝ := (b - u) * (c - u) / (a - u)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C u))) < 0 := by
  intro μ
  let sav : ℝ := a - u
  let dab : ℝ := b - a
  let dbc : ℝ := c - b
  have hsav_ne : sav ≠ 0 := ne_of_gt (by dsimp [sav]; linarith)
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u))
  have hshift : cubicDiscr P = cubicDiscr (P.comp (X + C u)) := by
    dsimp [P]
    rw [cubicSubQuadratic_eq_cubic_expansion]
    exact
      (cubicDiscr_cubic_comp_X_add_C
        1 (-(a + b + c + μ))
        (a * b + a * c + b * c + μ * (u + u))
        (-(a * b * c) - μ * (u * u)) u).symm
  have hcomp_eq :
      P.comp (X + C u) =
        ((X - C sav) * (X - C (sav + dab)) *
            (X - C (sav + dab + dbc))) -
          C ((sav + dab) * (sav + dab + dbc) / sav) *
            ((X - C 0) * (X - C 0)) := by
    dsimp [P]
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    dsimp [μ, sav, dab, dbc]
    field_simp [hsav_ne]
    ring_nf
  have hdisc_eq :
      cubicDiscr P =
        -(cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc / sav ^ 2) := by
    rw [hshift, hcomp_eq]
    exact cubicDiscr_cubicSubQuadratic_left_double_roots_below_norm
      sav dab dbc hsav_ne
  change cubicDiscr P < 0
  rw [hdisc_eq]
  have hsav_pos : 0 < sav := by
    dsimp [sav]
    linarith
  have hdab_nonneg : 0 ≤ dab := by
    dsimp [dab]
    linarith
  have hdbc_nonneg : 0 ≤ dbc := by
    dsimp [dbc]
    linarith
  have hbracket : 0 < cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc :=
    cubicSubQuadraticLeftDoubleBelowBracket_pos hsav_pos hdab_nonneg hdbc_nonneg
  have hfrac :
      0 < cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc / sav ^ 2 :=
    div_pos hbracket (by positivity)
  nlinarith

/-- If the quadratic has a double root strictly below the cubic roots, then
some positive subtraction coefficient makes the monic cubic-minus-quadratic
pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_left_double_roots_below
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C u))).Splits := by
  let μ : ℝ := (b - u) * (c - u) / (a - u)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_left_double_roots_below_mu_pos hab hbc hua
  refine ⟨μ, hμ, ?_⟩
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C u))).natDegree ≤ 3 := by
    rw [natDegree_cubicSubQuadratic]
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C u))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_left_double_roots_below_neg hab hbc hua
  intro hsplit
  exact (not_le.mpr hdisc)
    (cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit)

/-- The cubic/linear factor endpoint is not compatible when the leading
coefficients have opposite signs and the linear root lies strictly above the
cubic root interval. -/
lemma not_compatible_scaled_cubic_linear_of_opposite_of_upper_lt_right_root
    {a b c u A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcu : c < u) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * (X - C u)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubLinear_not_splits_of_upper_lt_right_root hab hbc hcu
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / B) * (C B * (X - C u)) =
          -((((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b) * (X - C c)) -
              C μ * (X - C u) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / (-B)) * (C B * (X - C u)) =
          ((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- The cubic/linear factor endpoint is not compatible when the leading
coefficients have opposite signs and the linear root lies strictly below the
cubic root interval. -/
lemma not_compatible_scaled_cubic_linear_of_opposite_of_left_root_lt_lower
    {a b c u A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * (X - C u)) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubLinear_not_splits_of_left_root_lt_lower hab hbc hua
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / B) * (C B * (X - C u)) =
          -((((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b) * (X - C c)) -
              C μ * (X - C u) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / (-B)) * (C B * (X - C u)) =
          ((X - C a) * (X - C b) * (X - C c)) -
            C μ * (X - C u) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and the average of the quadratic roots lies
strictly above the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_average_above
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcmean : c < (u + v) / 2) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_average_above hab hbc hcmean
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / B) * (C B * ((X - C u) * (X - C v))) =
          -((((X - C a) * (X - C b) * (X - C c)) -
            C μ * ((X - C u) * (X - C v)))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b) * (X - C c)) -
              C μ * ((X - C u) * (X - C v)) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / (-B)) * (C B * ((X - C u) * (X - C v))) =
          ((X - C a) * (X - C b) * (X - C c)) -
            C μ * ((X - C u) * (X - C v)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and both quadratic roots lie strictly above
the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_right_roots_above
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcu : c < u) (huv : u ≤ v) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_average_above
      hAB hab hbc hcmean

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and the two distinct quadratic roots lie
strictly below the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below_strict
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u < v) (hva : v < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_left_roots_below_strict
      hab hbc huv hva
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / B) * (C B * ((X - C u) * (X - C v))) =
          -((((X - C a) * (X - C b) * (X - C c)) -
            C μ * ((X - C u) * (X - C v)))) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' :
          ((X - C a) * (X - C b) * (X - C c)) -
              C μ * ((X - C u) * (X - C v)) = 0 := by
        rw [← neg_eq_zero]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) *
              (C A * ((X - C a) * (X - C b) * (X - C c))) +
            C (μ / (-B)) * (C B * ((X - C u) * (X - C v))) =
          ((X - C a) * (X - C b) * (X - C c)) -
            C μ * ((X - C u) * (X - C v)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

private lemma not_compatible_scaled_pair_of_opposite_of_sub_not_splits
    {P Q : ℝ[X]} {A B μ : ℝ} (hAB : A * B < 0) (hμ : 0 < μ)
    (hnot_splits : ¬ (P - C μ * Q).Splits) :
    ¬ Compatible (C A * P) (C B * Q) := by
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) * (C A * P) + C (μ / B) * (C B * Q) =
          -(P - C μ * Q) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' : P - C μ * Q = 0 := by
        rw [← neg_eq_zero]
        simpa using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) * (C A * P) + C (μ / (-B)) * (C B * Q) =
          P - C μ * Q := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

private lemma not_compatible_scaled_common_factor_of_opposite_of_sub_not_splits
    {D P Q : ℝ[X]} {A B μ : ℝ} (hD_ne : D ≠ 0) (hD_splits : D.Splits)
    (hAB : A * B < 0) (hμ : 0 < μ)
    (hnot_splits : ¬ (P - C μ * Q).Splits) :
    ¬ Compatible (C A * (D * P)) (C B * (D * Q)) := by
  have hnot_product : ¬ (D * (P - C μ * Q)).Splits := by
    intro hsplits
    exact hnot_splits ((splits_mul_iff_right hD_ne hD_splits).mp hsplits)
  have hsub_eq : D * P - C μ * (D * Q) = D * (P - C μ * Q) := by
    ring
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := D * P) (Q := D * Q) hAB hμ (by
        intro hsplits
        exact hnot_product (by simpa [hsub_eq] using hsplits))

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs, the lower quadratic root lies weakly below
the cubic interval, and the upper quadratic root lies strictly above it. -/
lemma
    not_compatible_scaled_cubic_quadratic_of_opposite_of_right_protruding_left_below
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u ≤ a) (hcv : c < v) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_right_protruding_left_below
      hab hbc hua hcv
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and the quadratic has a double root strictly
below the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_left_double_roots_below
    {a b c u A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C u))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_left_double_roots_below hab hbc hua
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C u))
      hAB hμ hnot_splits

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs, the lower quadratic root is the middle cubic
root, and the upper quadratic root lies strictly above the cubic root interval.
-/
private lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_middle_common_root_upper
    {a b c v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcv : c < v) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C b) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubLinear_not_splits_of_upper_lt_right_root
      (a := a) (b := c) (c := v) (hab.trans hbc) hcv
  have hbad :
      ¬ Compatible
        (C A * ((X - C b) * ((X - C a) * (X - C c))))
        (C B * ((X - C b) * (X - C v))) :=
    not_compatible_scaled_common_factor_of_opposite_of_sub_not_splits
      (D := X - C b) (P := (X - C a) * (X - C c)) (Q := X - C v)
      (X_sub_C_ne_zero b) (Polynomial.Splits.X_sub_C b) hAB hμ hnot_splits
  intro hcompat
  exact hbad (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcompat)

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and both quadratic roots lie weakly below the
cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hva : v < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  by_cases huv_lt : u < v
  · exact
      not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below_strict
        hAB hab hbc huv_lt hva
  · have hvu : v ≤ u := le_of_not_gt huv_lt
    have huv_eq : u = v := le_antisymm huv hvu
    subst v
    exact
      not_compatible_scaled_cubic_quadratic_of_opposite_of_left_double_roots_below
        hAB hab hbc hva

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the case where the average of the quadratic roots lies strictly above
the cubic root interval. -/
lemma not_average_above_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    ¬ c < (u + v) / 2 := by
  intro hcmean
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac :
      g = C g.leadingCoeff * ((X - C u) * (X - C v)) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * ((X - C u) * (X - C v))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_average_above
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc hcmean hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the case where both quadratic roots lie strictly above the cubic
root interval. -/
lemma not_right_roots_above_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hfroots : f.roots = {a, b, c})
    (hgroots : g.roots = {u, v}) :
    ¬ c < u := by
  intro hcu
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact
    not_average_above_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc hfroots hgroots hcmean

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the right-protruding case when the lower quadratic root lies weakly
below the lower cubic root. -/
lemma not_right_protruding_left_below_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u ≤ a) (hfroots : f.roots = {a, b, c})
    (hgroots : g.roots = {u, v}) :
    ¬ c < v := by
  intro hcv
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac :
      g = C g.leadingCoeff * ((X - C u) * (X - C v)) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * ((X - C u) * (X - C v))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_right_protruding_left_below
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc hua hcv hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the right-protruding boundary case where the lower quadratic root is
the middle cubic root. -/
lemma not_right_protruding_middle_common_root_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hub : u = b) (hfroots : f.roots = {a, b, c})
    (hgroots : g.roots = {u, v}) :
    ¬ c < v := by
  subst u
  intro hcv
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac : g = C g.leadingCoeff * ((X - C b) * (X - C v)) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * ((X - C b) * (X - C v))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_middle_common_root_upper
      (A := f.leadingCoeff) (B := g.leadingCoeff) hsgn hab hbc hcv hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, if the lower
quadratic root lies weakly below the lower cubic root, then the upper quadratic
root is at most the upper cubic root. -/
lemma upper_quadratic_root_le_upper_cubic_root_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u ≤ a) (hfroots : f.roots = {a, b, c})
    (hgroots : g.roots = {u, v}) :
    v ≤ c := by
  by_contra hnot
  exact
    not_right_protruding_left_below_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc hua hfroots hgroots
      (lt_of_not_ge hnot)

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the case where the two quadratic roots are distinct and both lie
strictly below the cubic root interval. -/
lemma not_left_roots_below_strict_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u < v) (hfroots : f.roots = {a, b, c})
    (hgroots : g.roots = {u, v}) :
    ¬ v < a := by
  intro hva
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac :
      g = C g.leadingCoeff * ((X - C u) * (X - C v)) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * ((X - C u) * (X - C v))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below_strict
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc huv hva hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the case where a double quadratic root lies strictly below the cubic
root interval. -/
lemma not_left_double_roots_below_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, u}) :
    ¬ u < a := by
  intro hua
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac :
      g = C g.leadingCoeff * ((X - C u) * (X - C u)) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * ((X - C u) * (X - C u))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_left_double_roots_below
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc hua hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the case where both quadratic roots lie weakly below the cubic root
interval. -/
lemma not_left_roots_below_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hfroots : f.roots = {a, b, c})
    (hgroots : g.roots = {u, v}) :
    ¬ v < a := by
  intro hva
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac :
      g = C g.leadingCoeff * ((X - C u) * (X - C v)) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * ((X - C u) * (X - C v))) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc huv hva hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, the lower cubic
root is at most the upper quadratic root. -/
lemma lower_cubic_root_le_upper_quadratic_root_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hfroots : f.roots = {a, b, c})
    (hgroots : g.roots = {u, v}) :
    a ≤ v := by
  by_contra hnot
  exact
    not_left_roots_below_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hfroots hgroots
      (lt_of_not_ge hnot)

/-- Compatible opposite-sign cubic/linear pairs have the linear root in the
closed interval spanned by the cubic roots. -/
theorem compatibleCubicLinearRootOrder :
    CompatibleCubicLinearRootOrderStatement := by
  intro f g a b c u hf hg hsgn hcompat hfdeg hgdeg hab hbc hfroots hgroots
  have hffac :
      f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) :=
    eq_C_leadingCoeff_mul_prod_three hf a b c hfroots
  have hgfac : g = C g.leadingCoeff * (X - C u) := by
    have hprod := hg.eq_prod_roots
    rw [hgroots] at hprod
    simpa using hprod
  have hcompat_fac :
      Compatible
        (C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)))
        (C g.leadingCoeff * (X - C u)) := by
    rw [← hffac, ← hgfac]
    exact hcompat
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hua : u < a := lt_of_not_ge hnot
    exact
      not_compatible_scaled_cubic_linear_of_opposite_of_left_root_lt_lower
        (A := f.leadingCoeff) (B := g.leadingCoeff)
        hsgn hab hbc hua hcompat_fac
  · by_contra hnot
    have hcu : c < u := lt_of_not_ge hnot
    exact
      not_compatible_scaled_cubic_linear_of_opposite_of_upper_lt_right_root
        (A := f.leadingCoeff) (B := g.leadingCoeff)
        hsgn hab hbc hcu hcompat_fac

/-- Checked degree `(3, 1)` no-common forward endpoint case. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_three_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 1) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_three_one_of_cubicLinearRootOrder
    compatibleCubicLinearRootOrder hf hg hsgn hcompat hfdeg hgdeg

/-- Checked degree `(1, 3)` no-common forward endpoint case. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_one_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg : f.natDegree = 1) (hgdeg : g.natDegree = 3) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_one_three_of_cubicLinearRootOrder
    compatibleCubicLinearRootOrder hf hg hsgn hcompat hno hfdeg hgdeg

/-- Conditional nonconstant no-common forward direction through endpoint
degree three, excluding the cubic/cubic corner and now using the checked
cubic/linear obstruction. -/
theorem
    theorem21RootCountBranches_of_natDegree_le_three_excluding_three_three_of_cubicPairRootOrder
    (hpair : CompatibleCubicPairRootOrderStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3)
    (hnot_three_three : ¬ (f.natDegree = 3 ∧ g.natDegree = 3)) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_le_three_excluding_three_three
    compatibleCubicLinearRootOrder hpair hf hg hsgn hcompat hno
    hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hnot_three_three

/-- Normalized monic arithmetic leaf for the degree-two/degree-three
right-successor positive-split x-subtraction endpoint. -/
def xSubQuadraticCubicSplitsStatement : Prop :=
  ∀ {a b c d e μ : ℝ},
    a ≤ b → c ≤ d → d ≤ e → c ≤ a → d ≤ b → a ≤ e →
      b ≤ 0 → e ≤ 0 → 0 < μ →
        (X * ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d) * (X - C e))).Splits

/-- Expanded form of the normalized quadratic/cubic endpoint polynomial. -/
lemma xSubQuadraticCubic_eq_cubic_expansion (a b c d e μ : ℝ) :
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e)) =
        C (1 - μ) * X ^ 3 + C (μ * (c + d + e) - (a + b)) * X ^ 2 +
          C (a * b - μ * (c * d + c * e + d * e)) * X +
            C (μ * c * d * e) := by
  simp only [C_add, C_sub, C_mul, C_1]
  ring_nf

/-- The normalized quadratic/cubic x-subtraction polynomial has degree at most
three. -/
lemma natDegree_xSubQuadraticCubic_le (a b c d e μ : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).natDegree ≤ 3 := by
  compute_degree

/-- When the top cubic terms cancel, the normalized quadratic/cubic
x-subtraction polynomial has degree at most two. -/
lemma natDegree_xSubQuadraticCubic_of_mu_one_le_two (a b c d e : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C (1 : ℝ) * ((X - C c) * (X - C d) * (X - C e))).natDegree ≤ 2 := by
  rw [xSubQuadraticCubic_eq_cubic_expansion]
  simp only [sub_self, map_zero, zero_mul, one_mul, map_sub, map_add, zero_add,
    map_mul]
  compute_degree

/-- Cubic coefficient of the normalized quadratic/cubic endpoint polynomial. -/
lemma coeff_three_xSubQuadraticCubic (a b c d e μ : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).coeff 3 = 1 - μ := by
  rw [xSubQuadraticCubic_eq_cubic_expansion]
  simp [Polynomial.coeff_mul_X_pow']

/-- Away from the cancellation value `μ = 1`, the normalized quadratic/cubic
x-subtraction polynomial is a genuine cubic. -/
lemma natDegree_xSubQuadraticCubic_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_xSubQuadraticCubic_le a b c d e μ
  · rw [coeff_three_xSubQuadraticCubic]
    intro h
    exact hμ (by linarith)

/-- Away from the cancellation value `μ = 1`, the normalized quadratic/cubic
x-subtraction polynomial is nonzero. -/
lemma xSubQuadraticCubic_ne_zero_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubQuadraticCubic_of_mu_ne_one a b c d e μ hμ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- Leading coefficient of the normalized quadratic/cubic endpoint polynomial
away from the cancellation value `μ = 1`. -/
lemma leadingCoeff_xSubQuadraticCubic_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).leadingCoeff = 1 - μ := by
  rw [Polynomial.leadingCoeff,
    natDegree_xSubQuadraticCubic_of_mu_ne_one a b c d e μ hμ,
    coeff_three_xSubQuadraticCubic]

/-- Positive-leading case for the normalized quadratic/cubic endpoint
polynomial. -/
lemma hasPosLeadingCoeff_xSubQuadraticCubic_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff_xSubQuadraticCubic_of_mu_ne_one]
  · linarith
  · exact ne_of_lt hμ

/-- Negative-leading case, expressed as positivity of the negated normalized
quadratic/cubic endpoint polynomial. -/
lemma hasPosLeadingCoeff_neg_xSubQuadraticCubic_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    HasPosLeadingCoeff
      (-(X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e)))) := by
  unfold HasPosLeadingCoeff
  rw [Polynomial.leadingCoeff_neg, leadingCoeff_xSubQuadraticCubic_of_mu_ne_one]
  · linarith
  · exact ne_of_gt hμ

/-- Evaluation form of the normalized quadratic/cubic x-subtraction leaf. -/
lemma eval_xSubQuadraticCubic (a b c d e μ x : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).eval x =
      x * ((x - a) * (x - b)) - μ * ((x - c) * (x - d) * (x - e)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- If `μ < 1`, the normalized quadratic/cubic endpoint polynomial tends to
`+∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atTop_atTop_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuadraticCubic_of_mu_lt_one a b c d e μ hμ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
      · norm_num
      · exact ne_of_lt hμ
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- If `μ < 1`, the normalized quadratic/cubic endpoint polynomial tends to
`-∞` at `-∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atBot_atBot_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atBot atBot := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuadraticCubic_of_mu_lt_one a b c d e μ hμ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
      · norm_num
      · exact ne_of_lt hμ
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_odd : Odd P.natDegree := by
    dsimp [P]
    rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
    · norm_num
    · exact ne_of_lt hμ
  exact tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hP_pos hP_deg_pos hP_odd

/-- If `1 < μ`, the normalized quadratic/cubic endpoint polynomial tends to
`+∞` at `-∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atBot_atTop_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atBot atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  let Q : ℝ[X] := -P
  have hQ_pos : HasPosLeadingCoeff Q := by
    dsimp [Q, P]
    exact hasPosLeadingCoeff_neg_xSubQuadraticCubic_of_one_lt_mu a b c d e μ hμ
  have hQ_deg_pos : 0 < Q.degree := by
    have hnat : 0 < Q.natDegree := by
      dsimp [Q, P]
      rw [Polynomial.natDegree_neg]
      rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
      · norm_num
      · exact ne_of_gt hμ
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hQ_odd : Odd Q.natDegree := by
    dsimp [Q, P]
    rw [Polynomial.natDegree_neg]
    rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
    · norm_num
    · exact ne_of_gt hμ
  have htQ : Tendsto (fun x => Q.eval x) atBot atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hQ_pos hQ_deg_pos hQ_odd
  have htneg := tendsto_neg_atBot_atTop.comp htQ
  convert htneg using 1
  ext x
  dsimp [Q]
  rw [eval_neg]
  simp only [eval_sub, eval_mul, eval_X, eval_C, neg_neg]
  rw [eval_xSubQuadraticCubic]

/-- If `1 < μ`, the normalized quadratic/cubic endpoint polynomial tends to
`-∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atTop_atBot_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atTop atBot := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  let Q : ℝ[X] := -P
  have hQ_pos : HasPosLeadingCoeff Q := by
    dsimp [Q, P]
    exact hasPosLeadingCoeff_neg_xSubQuadraticCubic_of_one_lt_mu a b c d e μ hμ
  have hQ_deg_pos : 0 < Q.degree := by
    have hnat : 0 < Q.natDegree := by
      dsimp [Q, P]
      rw [Polynomial.natDegree_neg]
      rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
      · norm_num
      · exact ne_of_gt hμ
    exact natDegree_pos_iff_degree_pos.mp hnat
  have htQ : Tendsto (fun x => Q.eval x) atTop atTop :=
    Q.tendsto_atTop_of_leadingCoeff_nonneg hQ_deg_pos hQ_pos.le
  have htneg := tendsto_neg_atTop_atBot.comp htQ
  convert htneg using 1
  ext x
  dsimp [Q]
  rw [eval_neg]
  simp only [eval_sub, eval_mul, eval_X, eval_C, neg_neg]
  rw [eval_xSubQuadraticCubic]

/-- The common splitting tail for the normalized quadratic/cubic endpoint:
two ordered finite roots, a negative value to their left, and a negative value
at zero imply splitting.  The proof splits on the leading coefficient:
`μ < 1` gives a right outer root, `1 < μ` gives a left outer root, and
`μ = 1` drops the degree to at most two. -/
lemma xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    {a b c d e μ l r₁ r₂ : ℝ}
    (hleft_neg :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).eval l < 0)
    (hzero_neg :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).eval 0 < 0)
    (hl1 : l < r₁) (h12 : r₁ < r₂) (hr2_0 : r₂ < 0)
    (hr₁ :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).IsRoot r₁)
    (hr₂ :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).IsRoot r₂) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hP_left_neg : P.eval l < 0 := by simpa [P] using hleft_neg
  have hP_zero_neg : P.eval 0 < 0 := by simpa [P] using hzero_neg
  have hP_r₁ : P.IsRoot r₁ := by simpa [P] using hr₁
  have hP_r₂ : P.IsRoot r₂ := by simpa [P] using hr₂
  rcases lt_trichotomy μ 1 with hμ_lt | hμ_eq | hμ_gt
  · have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
      dsimp [P]
      exact
        tendsto_eval_xSubQuadraticCubic_atTop_atTop_of_mu_lt_one
          a b c d e μ hμ_lt
    obtain ⟨rR, hrR_ge, hrR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
        (le_of_lt hP_zero_neg) ht_top
    have h2R : r₂ < rR := lt_of_lt_of_le hr2_0 hrR_ge
    have hP_ne : P ≠ 0 := by
      dsimp [P]
      exact xSubQuadraticCubic_ne_zero_of_mu_ne_one
        a b c d e μ (ne_of_lt hμ_lt)
    have hdeg_le : P.natDegree ≤ 3 := by
      dsimp [P]
      exact natDegree_xSubQuadraticCubic_le a b c d e μ
    have hsplits := splits_of_three_ordered_roots_of_natDegree_le
      hP_ne hdeg_le h12 h2R hP_r₁ hP_r₂ hrR_root
    simpa [P] using hsplits
  · have hP_ne : P ≠ 0 := by
      intro hzero
      have hroot : P.eval l = 0 := by simp [hzero]
      linarith
    have hdeg_le : P.natDegree ≤ 2 := by
      dsimp [P]
      rw [hμ_eq]
      exact natDegree_xSubQuadraticCubic_of_mu_one_le_two a b c d e
    have hsplits := splits_of_roots_list_of_natDegree_le (rs := [r₁, r₂])
      hP_ne (by simpa using hdeg_le)
      (by simp [ne_of_lt h12])
      (by
        intro r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact hP_r₁
        · exact hP_r₂)
    simpa [P] using hsplits
  · have ht_bot : Tendsto (fun x => P.eval x) atBot atTop := by
      dsimp [P]
      exact
        tendsto_eval_xSubQuadraticCubic_atBot_atTop_of_one_lt_mu
          a b c d e μ hμ_gt
    obtain ⟨rL, hrL_le, hrL_root⟩ :=
      exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop
        (le_of_lt hP_left_neg) ht_bot
    have hL1 : rL < r₁ := lt_of_le_of_lt hrL_le hl1
    have hP_ne : P ≠ 0 := by
      dsimp [P]
      exact xSubQuadraticCubic_ne_zero_of_mu_ne_one
        a b c d e μ (ne_of_gt hμ_gt)
    have hdeg_le : P.natDegree ≤ 3 := by
      dsimp [P]
      exact natDegree_xSubQuadraticCubic_le a b c d e μ
    have hsplits := splits_of_three_ordered_roots_of_natDegree_le
      hP_ne hdeg_le hL1 h12 hrL_root hP_r₁ hP_r₂
    simpa [P] using hsplits

/-- Strict ordinary interleaving case `c < a < d < b < e < 0` for the
normalized quadratic/cubic leaf.  The proof uses the two finite sign changes
between `(a, d)` and `(b, e)`.  The third root is on the right when `μ < 1`,
on the left when `1 < μ`, and unnecessary when the cubic term cancels at
`μ = 1`. -/
lemma xSubQuadraticCubicSplits_of_order_c_a_d_b_e
    {a b c d e μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hbe : b < e) (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hcd : c < d := lt_trans hca had
  have hde : d < e := lt_trans hdb hbe
  have hcb : c < b := lt_trans hcd hdb
  have hae : a < e := lt_trans had hde
  have hb0 : b < 0 := lt_trans hbe he0
  have hd0 : d < 0 := lt_trans hdb hb0
  have ha0 : a < 0 := lt_trans had hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have htail_pos : 0 < (a - d) * (a - e) :=
      mul_pos_of_neg_of_neg had_neg hae_neg
    have hG_pos : 0 < (a - c) * (a - d) * (a - e) := by
      nlinarith [mul_pos hac_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_neg : b - e < 0 := sub_neg.mpr hbe
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_neg : (b - c) * (b - d) * (b - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hbe_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_pos : 0 < e - b := sub_pos.mpr hbe
    have hprod_pos : 0 < (e - a) * (e - b) := mul_pos hea_pos heb_pos
    have hleft_neg : e * ((e - a) * (e - b)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg had
      (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
  obtain ⟨r₂, hb_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbe
      (mul_neg_of_pos_of_neg hP_b_pos hP_e_neg)
  have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_d (lt_trans hdb hb_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict nonordinary case `c < d < a < b < e < 0` for the normalized
quadratic/cubic leaf.  This is parallel to
`xSubQuadraticCubicSplits_of_order_c_a_d_b_e`, with the first finite sign
change on `(d, a)`. -/
lemma xSubQuadraticCubicSplits_of_order_c_d_a_b_e
    {a b c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hab : a < b)
    (hbe : b < e) (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hca : c < a := lt_trans hcd hda
  have hdb : d < b := lt_trans hda hab
  have hde : d < e := lt_trans hdb hbe
  have hcb : c < b := lt_trans hca hab
  have hae : a < e := lt_trans hab hbe
  have hb0 : b < 0 := lt_trans hbe he0
  have ha0 : a < 0 := lt_trans hab hb0
  have hd0 : d < 0 := lt_trans hda ha0
  have hc0 : c < 0 := lt_trans hcd hd0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_neg : d - a < 0 := sub_neg.mpr hda
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_pos : 0 < (d - a) * (d - b) :=
      mul_pos_of_neg_of_neg hda_neg hdb_neg
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_pos : 0 < a - d := sub_pos.mpr hda
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
    have hG_neg : (a - c) * (a - d) * (a - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hae_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_neg : b - e < 0 := sub_neg.mpr hbe
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_neg : (b - c) * (b - d) * (b - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hbe_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_pos : 0 < e - b := sub_pos.mpr hbe
    have hprod_pos : 0 < (e - a) * (e - b) := mul_pos hea_pos heb_pos
    have hleft_neg : e * ((e - a) * (e - b)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hda
      (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
  obtain ⟨r₂, hb_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbe
      (mul_neg_of_pos_of_neg hP_b_pos hP_e_neg)
  have hleft_r₁ : c < r₁ := lt_trans hcd hd_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hab hb_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict endpoint order `c < a < d < e < b < 0` for the normalized
quadratic/cubic leaf.  The first finite sign change is on `(a, d)`, while the
second is on `(e, b)`. -/
lemma xSubQuadraticCubicSplits_of_order_c_a_d_e_b
    {a b c d e μ : ℝ} (hca : c < a) (had : a < d) (hde : d < e)
    (heb : e < b) (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hcd : c < d := lt_trans hca had
  have hdb : d < b := lt_trans hde heb
  have hcb : c < b := lt_trans hcd hdb
  have hae : a < e := lt_trans had hde
  have he0 : e < 0 := lt_trans heb hb0
  have hd0 : d < 0 := lt_trans hde he0
  have ha0 : a < 0 := lt_trans had hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have htail_pos : 0 < (a - d) * (a - e) :=
      mul_pos_of_neg_of_neg had_neg hae_neg
    have hG_pos : 0 < (a - c) * (a - d) * (a - e) := by
      nlinarith [mul_pos hac_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_neg : e - b < 0 := sub_neg.mpr heb
    have hprod_neg : (e - a) * (e - b) < 0 :=
      mul_neg_of_pos_of_neg hea_pos heb_neg
    have hleft_pos : 0 < e * ((e - a) * (e - b)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_pos : 0 < b - e := sub_pos.mpr heb
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_pos : 0 < (b - c) * (b - d) * (b - e) :=
      mul_pos hhead_pos hbe_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg had
      (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
  obtain ⟨r₂, he_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg heb
      (mul_neg_of_pos_of_neg hP_e_pos hP_b_neg)
  have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_d (lt_trans hde he_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict endpoint order `c < d < a < e < b < 0` for the normalized
quadratic/cubic leaf.  This is the remaining strict total order compatible with
the endpoint inequalities. -/
lemma xSubQuadraticCubicSplits_of_order_c_d_a_e_b
    {a b c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hae : a < e)
    (heb : e < b) (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hca : c < a := lt_trans hcd hda
  have hdb : d < b := lt_trans (lt_trans hda hae) heb
  have hcb : c < b := lt_trans hcd hdb
  have hde : d < e := lt_trans hda hae
  have he0 : e < 0 := lt_trans heb hb0
  have hd0 : d < 0 := lt_trans hde he0
  have hc0 : c < 0 := lt_trans hcd hd0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_neg : d - a < 0 := sub_neg.mpr hda
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_pos : 0 < (d - a) * (d - b) :=
      mul_pos_of_neg_of_neg hda_neg hdb_neg
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_pos : 0 < a - d := sub_pos.mpr hda
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
    have hG_neg : (a - c) * (a - d) * (a - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hae_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_neg : e - b < 0 := sub_neg.mpr heb
    have hprod_neg : (e - a) * (e - b) < 0 :=
      mul_neg_of_pos_of_neg hea_pos heb_neg
    have hleft_pos : 0 < e * ((e - a) * (e - b)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_pos : 0 < b - e := sub_pos.mpr heb
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_pos : 0 < (b - c) * (b - d) * (b - e) :=
      mul_pos hhead_pos hbe_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hda
      (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
  obtain ⟨r₂, he_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg heb
      (mul_neg_of_pos_of_neg hP_e_pos hP_b_neg)
  have hleft_r₁ : c < r₁ := lt_trans hcd hd_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hae he_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict shared-root-free quadratic/cubic endpoint data reduces to one of
the four strict total orders. -/
lemma xSubQuadraticCubicSplits_of_strict_no_common_middle_roots
    {a b c d e μ : ℝ} (hab : a < b) (hcd : c < d) (hde : d < e)
    (hca : c < a) (hdb : d < b) (hae : a < e)
    (had_ne : a ≠ d) (hbe_ne : b ≠ e) (hb0 : b < 0) (he0 : e < 0)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  rcases lt_or_gt_of_ne had_ne with had | hda
  · rcases lt_or_gt_of_ne hbe_ne with hbe | heb
    · exact xSubQuadraticCubicSplits_of_order_c_a_d_b_e
        hca had hdb hbe he0 hμ
    · exact xSubQuadraticCubicSplits_of_order_c_a_d_e_b
        hca had hde heb hb0 hμ
  · rcases lt_or_gt_of_ne hbe_ne with hbe | heb
    · exact xSubQuadraticCubicSplits_of_order_c_d_a_b_e
        hcd hda hab hbe he0 hμ
    · exact xSubQuadraticCubicSplits_of_order_c_d_a_e_b
        hcd hda hae heb hb0 hμ

/-- A difference of two monic quadratics splits when their roots satisfy the
weak endpoint inequalities appearing in the quadratic/cubic boundary case. -/
lemma quadraticSubQuadratic_splits_of_roots_le
    {a b c d μ : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hca : c ≤ a) (hdb : d ≤ b) (hμ : 0 < μ) :
    (((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  have hpoly :
      ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d)) =
        C (1 - μ) * X ^ 2 + C (-(a + b) + μ * (c + d)) * X +
          C (a * b - μ * (c * d)) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1]
    ring_nf
  have hdisc :
      0 ≤ discrim (1 - μ) (-(a + b) + μ * (c + d))
        (a * b - μ * (c * d)) := by
    by_cases hda : d ≤ a
    · let u : ℝ := d - c
      let v : ℝ := a - d
      let w : ℝ := b - a
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hw : 0 ≤ w := by
        dsimp [w]
        linarith
      have hdisc_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + d))
              (a * b - μ * (c * d)) =
            (μ * u + w) ^ 2 + 4 * μ * v * (u + v + w) := by
        dsimp [u, v, w]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
    · have had : a ≤ d := le_of_not_ge hda
      let u : ℝ := a - c
      let v : ℝ := d - a
      let w : ℝ := b - d
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hw : 0 ≤ w := by
        dsimp [w]
        linarith
      have hdisc_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + d))
              (a * b - μ * (c * d)) =
            (μ * (u + v) - (v + w)) ^ 2 + 4 * μ * u * w := by
        dsimp [u, v, w]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg_or_linear hdisc

/-- Boundary case where the upper cubic root is zero.  Factoring out `X`
leaves a difference of two monic quadratics. -/
lemma xSubQuadraticCubicSplits_of_right_root_zero
    {a b c d μ : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hca : c ≤ a) (hdb : d ≤ b) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * X)).Splits := by
  have hquad :
      (((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))).Splits :=
    quadraticSubQuadratic_splits_of_roots_le hab hcd hca hdb hμ
  have hfactor :
      X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * X) =
          X * (((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d))) := by
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hquad

/-- Common-root boundary for the normalized quadratic/cubic leaf.  Factoring
out the shared linear factor leaves the already proved linear/quadratic
x-subtraction endpoint. -/
lemma xSubQuadraticCubicSplits_of_common_root
    {r s u v μ : ℝ} (huv : u ≤ v) (hus : u ≤ s)
    (hv0 : v ≤ 0) (hs0 : s ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * (X - C s)) -
      C μ * ((X - C r) * (X - C u) * (X - C v))).Splits := by
  have hquad :
      (X * (X - C s) - C μ * ((X - C u) * (X - C v))).Splits :=
    xSubLinearQuadraticSplits huv hus hv0 hs0 hμ
  have hfactor :
      X * ((X - C r) * (X - C s)) -
        C μ * ((X - C r) * (X - C u) * (X - C v)) =
          (X - C r) *
            (X * (X - C s) - C μ * ((X - C u) * (X - C v))) := by
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hquad

/-- Boundary case where the lower cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_lower_common_root
    {a b d e μ : ℝ} (hde : d ≤ e) (hdb : d ≤ b)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C a) * (X - C d) * (X - C e))).Splits :=
  xSubQuadraticCubicSplits_of_common_root
    (r := a) (s := b) (u := d) (v := e) hde hdb he0 hb0 hμ

/-- Boundary case where the middle cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_middle_common_root
    {a b c e μ : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hae : a ≤ e)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C a) * (X - C e))).Splits := by
  have hce : c ≤ e := hca.trans hae
  have hcb : c ≤ b := hca.trans hab
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := a) (s := b) (u := c) (v := e) hce hcb he0 hb0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the upper cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_left_upper_common_root
    {a b c d μ : ℝ} (hcd : c ≤ d) (hca : c ≤ a) (hda : d ≤ a)
    (hab : a ≤ b) (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C a))).Splits := by
  have hd0 : d ≤ 0 := hda.trans (hab.trans hb0)
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := a) (s := b) (u := c) (v := d) hcd (hca.trans hab)
    hd0 hb0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the middle cubic root is the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_right_middle_common_root
    {a b c e μ : ℝ} (hab : a ≤ b) (hce : c ≤ e) (hca : c ≤ a)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C b) * (X - C e))).Splits := by
  have ha0 : a ≤ 0 := hab.trans hb0
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := b) (s := a) (u := c) (v := e) hce hca he0 ha0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the upper cubic root is the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_upper_common_root
    {a b c d μ : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a)
    (hdb : d ≤ b) (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C b))).Splits := by
  have hd0 : d ≤ 0 := hdb.trans hb0
  have ha0 : a ≤ 0 := hab.trans hb0
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := b) (s := a) (u := c) (v := d) hcd hca hd0 ha0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the quadratic endpoint has a double root. -/
lemma xSubQuadraticCubicSplits_of_left_double_root
    {a c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hae : a < e)
    (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C a)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hca : c < a := lt_trans hcd hda
  have hd0 : d < 0 := lt_trans hda (lt_trans hae he0)
  have ha0 : a < 0 := lt_trans hae he0
  have hc0 : c < 0 := lt_trans hcd hd0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hprod_pos : 0 < (c - a) * (c - a) :=
      mul_pos_of_neg_of_neg hca_neg hca_neg
    have hleft_neg : c * ((c - a) * (c - a)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_neg : d - a < 0 := sub_neg.mpr hda
    have hprod_pos : 0 < (d - a) * (d - a) :=
      mul_pos_of_neg_of_neg hda_neg hda_neg
    have hleft_neg : d * ((d - a) * (d - a)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_pos : 0 < a - d := sub_pos.mpr hda
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
    have hG_neg : (a - c) * (a - d) * (a - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hae_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have hprod_pos : 0 < (e - a) * (e - a) := mul_pos hea_pos hea_pos
    have hleft_neg : e * ((e - a) * (e - a)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hda
      (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
  obtain ⟨r₂, ha_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hae
      (mul_neg_of_pos_of_neg hP_a_pos hP_e_neg)
  have hleft_r₁ : c < r₁ := lt_trans hcd hd_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_a ha_r₂
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the two lower cubic roots coincide. -/
lemma xSubQuadraticCubicSplits_of_lower_cubic_double_root
    {a b c e μ : ℝ} (hca : c < a) (hab : a ≤ b) (hbe : b < e)
    (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))
  have hcb : c < b := lt_of_lt_of_le hca hab
  have hae : a < e := lt_of_le_of_lt hab hbe
  have hb0 : b < 0 := lt_trans hbe he0
  have ha0 : a < 0 := lt_of_le_of_lt hab hb0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - c) := mul_pos hac_pos hac_pos
    have hG_neg : (a - c) * (a - c) * (a - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hae_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbe_neg : b - e < 0 := sub_neg.mpr hbe
    have hhead_pos : 0 < (b - c) * (b - c) := mul_pos hbc_pos hbc_pos
    have hG_neg : (b - c) * (b - c) * (b - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hbe_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_pos : 0 < e - b := sub_pos.mpr hbe
    have hprod_pos : 0 < (e - a) * (e - b) := mul_pos hea_pos heb_pos
    have hleft_neg : e * ((e - a) * (e - b)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - c) := mul_pos hzc_pos hzc_pos
    have hG_pos : 0 < (0 - c) * (0 - c) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, hb_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbe
      (mul_neg_of_pos_of_neg hP_b_pos hP_e_neg)
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_of_le_of_lt hab hb_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hc_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the two lower cubic roots coincide and the remaining
cubic root lies below the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_lower_cubic_double_root_right
    {a b c e μ : ℝ} (hca : c < a) (hae : a < e) (heb : e < b)
    (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))
  have hcb : c < b := lt_trans hca (lt_trans hae heb)
  have he0 : e < 0 := lt_trans heb hb0
  have ha0 : a < 0 := lt_trans hae he0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - c) := mul_pos hac_pos hac_pos
    have hG_neg : (a - c) * (a - c) * (a - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hae_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_neg : e - b < 0 := sub_neg.mpr heb
    have hprod_neg : (e - a) * (e - b) < 0 :=
      mul_neg_of_pos_of_neg hea_pos heb_neg
    have hleft_pos : 0 < e * ((e - a) * (e - b)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbe_pos : 0 < b - e := sub_pos.mpr heb
    have hhead_pos : 0 < (b - c) * (b - c) := mul_pos hbc_pos hbc_pos
    have hG_pos : 0 < (b - c) * (b - c) * (b - e) :=
      mul_pos hhead_pos hbe_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - c) := mul_pos hzc_pos hzc_pos
    have hG_pos : 0 < (0 - c) * (0 - c) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, he_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg heb
      (mul_neg_of_pos_of_neg hP_e_pos hP_b_neg)
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hae he_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hc_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the two upper cubic roots coincide. -/
lemma xSubQuadraticCubicSplits_of_upper_cubic_double_root
    {a b c d μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C d))
  have hcd : c < d := lt_trans hca had
  have hcb : c < b := lt_trans hcd hdb
  have hd0 : d < 0 := lt_trans hdb hb0
  have ha0 : a < 0 := lt_trans had hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have htail_pos : 0 < (a - d) * (a - d) :=
      mul_pos_of_neg_of_neg had_neg had_neg
    have hG_pos : 0 < (a - c) * (a - d) * (a - d) := by
      nlinarith [mul_pos hac_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have htail_pos : 0 < (b - d) * (b - d) := mul_pos hbd_pos hbd_pos
    have hG_pos : 0 < (b - c) * (b - d) * (b - d) := by
      nlinarith [mul_pos hbc_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - d) :=
      mul_pos hhead_pos hzd_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg had
      (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
  obtain ⟨r₂, hd_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hdb
      (mul_neg_of_pos_of_neg hP_d_pos hP_b_neg)
  have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_d hd_r₂
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the upper quadratic root is zero and no middle root is
shared. -/
lemma xSubQuadraticCubicSplits_of_left_root_zero
    {a c d e μ : ℝ} (hcd : c ≤ d) (hca : c < a) (hde : d ≤ e)
    (hae : a < e) (he0 : e < 0) (had_ne : a ≠ d) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C 0)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C 0)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hd0 : d < 0 := lt_of_le_of_lt hde he0
  have ha0 : a < 0 := lt_trans hae he0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hc_neg : c - 0 < 0 := by simpa using hc0
    have hprod_pos : 0 < (c - a) * (c - 0) :=
      mul_pos_of_neg_of_neg hca_neg hc_neg
    have hleft_neg : c * ((c - a) * (c - 0)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have he_neg : e - 0 < 0 := by simpa using he0
    have hprod_neg : (e - a) * (e - 0) < 0 :=
      mul_neg_of_pos_of_neg hea_pos he_neg
    have hleft_pos : 0 < e * ((e - a) * (e - 0)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  rcases lt_or_gt_of_ne had_ne with had | hda
  · have hP_a_neg : P.eval a < 0 := by
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hac_pos : 0 < a - c := sub_pos.mpr hca
      have had_neg : a - d < 0 := sub_neg.mpr had
      have hae_neg : a - e < 0 := sub_neg.mpr hae
      have htail_pos : 0 < (a - d) * (a - e) :=
        mul_pos_of_neg_of_neg had_neg hae_neg
      have hG_pos : 0 < (a - c) * (a - d) * (a - e) := by
        nlinarith [mul_pos hac_pos htail_pos]
      nlinarith [mul_pos hμ hG_pos]
    have hP_d_pos : 0 < P.eval d := by
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hda_pos : 0 < d - a := sub_pos.mpr had
      have hd_neg : d - 0 < 0 := by simpa using hd0
      have hprod_neg : (d - a) * (d - 0) < 0 :=
        mul_neg_of_pos_of_neg hda_pos hd_neg
      have hleft_pos : 0 < d * ((d - a) * (d - 0)) :=
        mul_pos_of_neg_of_neg hd0 hprod_neg
      nlinarith
    obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg had
        (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
    obtain ⟨r₂, he_r₂, hr₂_zero, hr₂_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg he0
        (mul_neg_of_pos_of_neg hP_e_pos hP_zero_neg)
    have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
    have h12 : r₁ < r₂ := lt_trans hr₁_d (lt_of_le_of_lt hde he_r₂)
    exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
      hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root
  · have hP_d_neg : P.eval d < 0 := by
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hda_neg : d - a < 0 := sub_neg.mpr hda
      have hd_neg : d - 0 < 0 := by simpa using hd0
      have hprod_pos : 0 < (d - a) * (d - 0) :=
        mul_pos_of_neg_of_neg hda_neg hd_neg
      have hleft_neg : d * ((d - a) * (d - 0)) < 0 :=
        mul_neg_of_neg_of_pos hd0 hprod_pos
      nlinarith
    have hP_a_pos : 0 < P.eval a := by
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hac_pos : 0 < a - c := sub_pos.mpr hca
      have had_pos : 0 < a - d := sub_pos.mpr hda
      have hae_neg : a - e < 0 := sub_neg.mpr hae
      have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
      have hG_neg : (a - c) * (a - d) * (a - e) < 0 :=
        mul_neg_of_pos_of_neg hhead_pos hae_neg
      nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
    obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg hda
        (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
    obtain ⟨r₂, he_r₂, hr₂_zero, hr₂_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg he0
        (mul_neg_of_pos_of_neg hP_e_pos hP_zero_neg)
    have hleft_r₁ : c < r₁ := lt_of_le_of_lt hcd hd_r₁
    have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hae he_r₂)
    exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
      hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- The normalized monic quadratic/cubic x-subtraction leaf. -/
theorem xSubQuadraticCubicSplits :
    xSubQuadraticCubicSplitsStatement := by
  intro a b c d e μ hab hcd hde hca hdb hae hb0 he0 hμ
  by_cases he_zero : e = 0
  · subst e
    simpa using xSubQuadraticCubicSplits_of_right_root_zero
      (a := a) (b := b) (c := c) (d := d) (μ := μ) hab hcd hca hdb hμ
  have he_lt : e < 0 := lt_of_le_of_ne he0 he_zero
  by_cases hca_eq : c = a
  · subst c
    exact xSubQuadraticCubicSplits_of_lower_common_root hde hdb hb0 he0 hμ
  by_cases had_eq : a = d
  · subst d
    exact xSubQuadraticCubicSplits_of_middle_common_root hca hab hae hb0 he0 hμ
  by_cases hae_eq : a = e
  · subst e
    have hda : d ≤ a := by simpa using hde
    exact xSubQuadraticCubicSplits_of_left_upper_common_root
      hcd hca hda hab hb0 hμ
  by_cases hdb_eq : d = b
  · subst b
    have hce : c ≤ e := hcd.trans hde
    exact xSubQuadraticCubicSplits_of_right_middle_common_root
      hab hce hca hb0 he0 hμ
  by_cases hbe_eq : b = e
  · subst e
    exact xSubQuadraticCubicSplits_of_upper_common_root
      hab hcd hca hdb hb0 hμ
  by_cases hb_zero : b = 0
  · subst b
    have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
    have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
    have hsplits := xSubQuadraticCubicSplits_of_left_root_zero
      hcd hca_lt hde hae_lt he_lt had_eq hμ
    simpa using hsplits
  have hb_lt : b < 0 := lt_of_le_of_ne hb0 hb_zero
  by_cases hcd_eq : c = d
  · subst d
    have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
    rcases lt_or_gt_of_ne hbe_eq with hbe | heb
    · exact xSubQuadraticCubicSplits_of_lower_cubic_double_root
        hca_lt hab hbe he_lt hμ
    · have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
      exact xSubQuadraticCubicSplits_of_lower_cubic_double_root_right
        hca_lt hae_lt heb hb_lt hμ
  by_cases hde_eq : d = e
  · subst e
    have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
    have had_lt : a < d := lt_of_le_of_ne hae had_eq
    have hdb_lt : d < b := lt_of_le_of_ne hdb hdb_eq
    exact xSubQuadraticCubicSplits_of_upper_cubic_double_root
      hca_lt had_lt hdb_lt hb_lt hμ
  by_cases hab_eq : a = b
  · subst b
    have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
    have hda_lt : d < a := lt_of_le_of_ne hdb hdb_eq
    have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
    exact xSubQuadraticCubicSplits_of_left_double_root
      hcd_lt hda_lt hae_lt he_lt hμ
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
  have hde_lt : d < e := lt_of_le_of_ne hde hde_eq
  have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
  have hdb_lt : d < b := lt_of_le_of_ne hdb hdb_eq
  have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
  exact xSubQuadraticCubicSplits_of_strict_no_common_middle_roots
    hab_lt hcd_lt hde_lt hca_lt hdb_lt hae_lt had_eq hbe_eq hb_lt he_lt hμ

/-- The normalized monic quadratic/cubic x-subtraction leaf implies the
degree-two/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, c, d, e, hab, hcd, hde, hproots, hqroots,
      hpfac, hqfac, hca, hdb, hae⟩ :=
    exists_roots_order_of_positiveSplitRootCountPair_two_three
      hpair hpdeg hqdeg
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn b hb_mem
  have he0 : e ≤ 0 := by
    have he_mem : e ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn e he_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C ν * ((X - C c) * (X - C d) * (X - C e))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hcd hde hca hdb hae hb0 he0 hν_pos
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfac, hqfac]
    dsimp [inner, ν, A, B]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hpair.left_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-two/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three_of_monic
    xSubQuadraticCubicSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-two right endpoint case for the right-successor sign-normalized
x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 1 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 2 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two
    (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Endpoint cases through right degree two for the right-successor
sign-normalized x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hone : g.natDegree = 1
  · exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
      hpair hfnn hgnn hdeg hone
  · have htwo : g.natDegree = 2 := by
      lia
    exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
      hpair hfnn hgnn hdeg htwo

/-- Degree-three right endpoint case for the right-successor sign-normalized
x-subtraction leaf, modulo the normalized monic quadratic/cubic leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 2 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 2 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 3 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Degree-three right endpoint case for the right-successor sign-normalized
x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    xSubQuadraticCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree three for the right-successor
sign-normalized x-subtraction leaf, modulo the normalized monic
quadratic/cubic leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_two : g.natDegree ≤ 2
  · exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
      hpair hfnn hgnn hdeg hle_two
  · have hthree : g.natDegree = 3 := by
      lia
    exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hthree

/-- Endpoint cases through right degree three for the right-successor
sign-normalized x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    xSubQuadraticCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-two right endpoint terminal as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree two as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint terminal as a predicate-restricted
right-successor positive-split x-sub family, modulo the normalized monic
quadratic/cubic leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint terminal as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    xSubQuadraticCubicSplits

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem
    positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    hmono

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three

/-- Pack the endpoint cases through degree three as a predicate-restricted
right-successor positive-split x-sub family, modulo the normalized monic
quadratic/cubic leaf. -/
theorem
positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree three as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    hpair hfnn hgnn hdeg hgdeg

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem
    positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three

/-- Guardrail for the factor-return route: multiplying the higher-degree
member of a simple quadratic/linear interlacing pair by `X` need not preserve
all-combinations real-rootedness.  Thus the Liu factor-return proof cannot use
a generic all-combinations strengthening of the translated `X * q` target. -/
theorem not_allComboRealRooted_X_mul_quadratic_linear_example :
    ¬ AllComboRealRooted
      (X * ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) (-(X + C (2 : ℝ))) := by
  intro hall
  let p : ℝ[X] :=
    C (1 : ℝ) * (X * ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) +
      C (-1 : ℝ) * (-(X + C (2 : ℝ)))
  have hp_splits : p.Splits := by
    simpa [p] using hall 1 (-1)
  have hp_deg : p.natDegree ≤ 3 := by
    dsimp [p]
    compute_degree!
  have hdisc_nonneg : 0 ≤ cubicDiscr p :=
    cubicDiscr_nonneg_of_splits_natDegree_le_three hp_deg hp_splits
  have hdisc_neg : cubicDiscr p < 0 := by
    norm_num [p, cubicDiscr, coeff_add, coeff_C_mul, coeff_neg, coeff_mul,
      Finset.antidiagonal, coeff_X, coeff_C, coeff_one]
  linarith

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and all-combinations factor-return
degree cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
      hcases)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and all-combinations
factor-return degree cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allComboDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and
all-combinations factor-return degree cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allComboDegreeCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
      hcases)

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
all-combinations factor-return degree cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allComboDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and left all-combinations
factor-return degree cases, with right cases supplied by symmetry. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_leftAllComboCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_leftCases
      hcases)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and left
all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_leftAllComboCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_leftAllComboCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and left
all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_leftAllComboCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_leftCases
      hcases)

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
left all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_leftAllComboCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_leftAllComboCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

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
    have hGdeg : P (-g).natDegree := by
      simpa [Polynomial.natDegree_neg] using hgdeg
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

/-- Pointwise right-family form of a translated left-branch Liu compatibility
target.  This separates endpoint splitting and coefficient scaling from the
degree-specific right-family leaves. -/
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

/-- A translated positive right-family leaf for any degree relation gives the
corresponding translated compatibility target by scaling an arbitrary
nonnegative linear combination. -/
theorem theorem21LeftFactorReturnTranslatedCompatible_of_rightFamilyRelation
    {R : ℕ → ℕ → Prop}
    (hright :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                ∀ μ : ℝ, 0 < μ →
                  (X * (deleteRootFactor f r).comp (X + C r) +
                      C μ * g.comp (X + C r)).Splits) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              Compatible
                (X * (deleteRootFactor f r).comp (X + C r))
                (g.comp (X + C r)) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft (hright hf hg hsgn hleft hdeg hcommon)

/-- Predicate-restricted translated positive right-family leaves for any
degree relation give the corresponding pointwise translated compatibility
target. -/
theorem theorem21LeftFactorReturnTranslatedCompatible_of_rightPredicateRelation
    {R : ℕ → ℕ → Prop} {P : ℕ → Prop}
    (hright :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                P g.natDegree →
                  ∀ μ : ℝ, 0 < μ →
                    (X * (deleteRootFactor f r).comp (X + C r) +
                        C μ * g.comp (X + C r)).Splits) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              P g.natDegree →
                Compatible
                  (X * (deleteRootFactor f r).comp (X + C r))
                  (g.comp (X + C r)) := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturnTranslatedCompatible_of_pointwiseRightFamily
    hf hg hsgn hleft (hright hf hg hsgn hleft hdeg hcommon hgdeg)

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

/-- Pointwise translated compatibility descent for a Liu left-branch
factor-return route. -/
theorem theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible
    {f g : ℝ[X]} {r s : ℝ}
    (hleft : LeftRootCountBranch f g r s)
    (htranslated :
      Compatible
        (X * (deleteRootFactor f r).comp (X + C r))
        (g.comp (X + C r))) :
    Compatible f g :=
  hleft.compatible_of_translated_restore htranslated

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

/-- A translated compatibility proof for any degree relation gives the
corresponding original left-branch factor-return proof.  This is the common
descent step behind the same-, successor-, and two-degree wrappers. -/
theorem theorem21LeftFactorReturn_of_translatedCompatibleRelation
    {R : ℕ → ℕ → Prop}
    (htranslated :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                Compatible
                  (X * (deleteRootFactor f r).comp (X + C r))
                  (g.comp (X + C r))) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              Compatible f g := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft
    (htranslated hf hg hsgn hleft hdeg hcommon)

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

/-- Predicate-restricted translated compatibility targets give the
corresponding predicate-restricted original factor-return targets. -/
theorem theorem21LeftFactorReturnPredicate_of_translatedCompatibleRelation
    {R : ℕ → ℕ → Prop} {P : ℕ → Prop}
    (htranslated :
      ∀ {f g : ℝ[X]} {r s : ℝ},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          LeftRootCountBranch f g r s →
            R f.natDegree g.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
                P g.natDegree →
                  Compatible
                    (X * (deleteRootFactor f r).comp (X + C r))
                    (g.comp (X + C r))) :
    ∀ {f g : ℝ[X]} {r s : ℝ},
      f.Splits → g.Splits → OppositeLeadingSigns f g →
        LeftRootCountBranch f g r s →
          R f.natDegree g.natDegree →
            (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
              P g.natDegree → Compatible f g := by
  intro f g r s hf hg hsgn hleft hdeg hcommon hgdeg
  exact theorem21LeftFactorReturn_of_pointwiseTranslatedCompatible hleft
    (htranslated hf hg hsgn hleft hdeg hcommon hgdeg)

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

/-- The three left-branch factor-return cases.  The right-branch cases follow
by symmetry. -/
def theorem21LeftFactorReturnDegreeCasesStatement : Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreeStatement

/-- Translated compatibility targets for all three left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedCompatibleStatement ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatibleStatement ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement

/-- Translated right-family targets for all three left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyStatement ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyStatement ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement

/-- Sign-normalized positive-split x-subtraction cases for the three Liu
left-branch restored-degree cases. -/
def positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement : Prop :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement ∧
    positiveSplitSameDegreeTranslatedXSubRightFamilyStatement ∧
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement

/-- Predicate-restricted sign-normalized positive-split x-subtraction cases
for the three Liu left-branch restored-degree cases. -/
def positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement P ∧
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P ∧
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement P

/-- Predicate-restricted x-subtraction case packages transport along endpoint
predicate implications. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        Q) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      P :=
  ⟨positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
      hPQ hQ.1,
    positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
      hPQ hQ.2.1,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement_of_imp
      hPQ hQ.2.2⟩

/-- A predicate-`True` x-subtraction case package gives the corresponding
ordinary x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCases_of_predicate_true
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun _ => True)) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement :=
  ⟨positiveSplitTranslatedXSubRightFamilyRelation_of_predicate_true
      hcases.1,
    positiveSplitTranslatedXSubRightFamilyRelation_of_predicate_true
      hcases.2.1,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_predicate_true
      hcases.2.2⟩

/-- An ordinary x-subtraction case package gives the corresponding
predicate-`True` x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_true_of_cases
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun _ => True) :=
  ⟨positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hcases.1,
    positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      hcases.2.1,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_true_of_xSub
      hcases.2.2⟩

/-- Unrestricted x-subtraction cases give the `P := True` x-subtraction case
package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_true_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun _ => True) :=
  positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_true_of_cases
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- Endpoint cases through degree two as a bundled predicate-restricted
x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_two :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun n => n ≤ 2) :=
  ⟨positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two,
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two,
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two⟩

/-- Endpoint cases through degree three as a bundled predicate-restricted
x-subtraction case package, modulo the normalized monic quartic/cubic leaf. -/
theorem
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  ⟨positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three,
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three,
    positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
      hmono⟩

/-- Endpoint cases through degree three as a bundled predicate-restricted
x-subtraction case package. -/
theorem positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three :
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
    xSubQuarticCubicSplits

/-- Predicate-restricted translated compatibility targets for all three
left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement
        P

/-- Predicate-restricted translated right-family targets for all three
left-branch degree cases. -/
def theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement
        P

/-- Predicate-restricted translated compatibility case packages transport
along endpoint predicate implications. -/
theorem
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        Q) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
      P :=
  ⟨fun hf hg hsgn hleft hdeg hcommon hgdeg =>
      hQ.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg),
    fun hf hg hsgn hleft hdeg hcommon hgdeg =>
      hQ.2.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg),
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicateStatement_of_imp
      hPQ hQ.2.2⟩

/-- Predicate-restricted translated right-family case packages transport
along endpoint predicate implications. -/
theorem
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        Q) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
      P :=
  ⟨fun hf hg hsgn hleft hdeg hcommon hgdeg μ hμ =>
      hQ.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg) μ hμ,
    fun hf hg hsgn hleft hdeg hcommon hgdeg μ hμ =>
      hQ.2.1 hf hg hsgn hleft hdeg hcommon (hPQ _ hgdeg) μ hμ,
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicateStatement_of_imp
      hPQ hQ.2.2⟩

/-- Left all-combinations factor-return degree cases give the corresponding
compatibility factor-return degree cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_allComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegree_of_allCombo hcases.1,
    theorem21LeftFactorReturnSuccDegree_of_allCombo hcases.2.1,
    theorem21LeftFactorReturnTwoDegree_of_allCombo hcases.2.2⟩

/-- Translated left factor-return degree cases give the corresponding original
compatibility factor-return degree cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_translatedCompatibleCases
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegree_of_translatedCompatible hcases.1,
    theorem21LeftFactorReturnSuccDegree_of_translatedCompatible hcases.2.1,
    theorem21LeftFactorReturnTwoDegree_of_translatedCompatible hcases.2.2⟩

/-- Translated right-family degree cases give translated compatibility degree
cases. -/
theorem theorem21LeftFactorReturnTranslatedCompatibleCases_of_rightFamilyCases
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_rightFamily
      hcases.1,
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_rightFamily
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightFamily
      hcases.2.2⟩

/-- Predicate-restricted translated right-family degree cases give
predicate-restricted translated compatibility degree cases. -/
theorem
    theorem21LeftFactorReturnTranslatedCompatibleCasesPredicate_of_rightFamilyCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
      P :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hcases.1,
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatiblePredicate_of_rightPredicate
      hcases.2.2⟩

/-- Translated right-family degree cases give the corresponding original
compatibility factor-return degree cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_translatedRightFamilyCases
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_translatedCompatibleCases
    (theorem21LeftFactorReturnTranslatedCompatibleCases_of_rightFamilyCases
      hcases)

/-- Positive-split x-subtraction degree cases give translated right-family
degree cases for the three Liu left branches.  The same-degree Liu branch uses
the right-successor terminal, the successor-degree branch uses the same-degree
terminal, and the two-degree branch uses the left-successor terminal. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyCases_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedRightFamily_of_xSub
      hcases.1,
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamily_of_xSub
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub
      hcases.2.2⟩

/-- Positive-split x-subtraction degree cases give translated right-family
degree cases for the three Liu left branches.  The same-degree Liu branch uses
the right-successor terminal, the successor-degree branch uses the same-degree
terminal, and the two-degree branch uses the left-successor terminal. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyCases_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement :=
  theorem21LeftFactorReturnTranslatedRightFamilyCases_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- Sign-normalized positive-split x-subtraction cases give translated
compatibility cases for the three Liu left branches. -/
theorem theorem21LeftFactorReturnTranslatedCompatibleCases_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedCompatible_of_xSub
      hrightSucc,
    theorem21LeftFactorReturnSuccDegreeTranslatedCompatible_of_xSub hsame,
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_xSub
      hleftSucc⟩

/-- A bundled sign-normalized positive-split x-subtraction case package gives
translated compatibility cases for the three Liu left branches. -/
theorem theorem21LeftFactorReturnTranslatedCompatibleCases_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement :=
  theorem21LeftFactorReturnTranslatedCompatibleCases_of_xSubCases
    hcases.1 hcases.2.1 hcases.2.2

/-- Sign-normalized positive-split x-subtraction cases give the three original
left-branch factor-return cases directly. -/
theorem theorem21LeftFactorReturnDegreeCases_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨theorem21LeftFactorReturnSameDegree_of_xSub hrightSucc,
    theorem21LeftFactorReturnSuccDegree_of_xSub hsame,
    theorem21LeftFactorReturnTwoDegree_of_xSub hleftSucc⟩

/-- A bundled sign-normalized positive-split x-subtraction case package gives
the three original left-branch factor-return cases. -/
theorem theorem21LeftFactorReturnDegreeCases_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_xSubCases
    hcases.1 hcases.2.1 hcases.2.2

/-- Predicate-restricted positive-split x-subtraction degree cases give
predicate-restricted translated right-family degree cases for the three Liu
left branches. -/
theorem theorem21LeftFactorReturnTranslatedRightFamilyCasesPredicate_of_xSubCasesPredicate
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
      P :=
  ⟨theorem21LeftFactorReturnSameDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hrightSucc,
    theorem21LeftFactorReturnSuccDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hsame,
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyPredicate_of_xSubPredicate
      hleftSucc⟩

/-- Bundled predicate-restricted positive-split x-subtraction cases give
predicate-restricted translated right-family degree cases. -/
theorem
    theorem21LeftFactorReturnTranslatedRightFamilyCasesPredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
      P :=
  theorem21LeftFactorReturnTranslatedRightFamilyCasesPredicate_of_xSubCasesPredicate
    hcases.1 hcases.2.1 hcases.2.2

/-- Same-degree and succ-degree leaves plus the translated two-degree target
give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hsame, hsucc,
    theorem21LeftFactorReturnTwoDegree_of_translatedCompatible htwo⟩

/-- Same-degree and succ-degree leaves plus the translated right-family
two-degree target give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_rightFamily
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hsame, hsucc, theorem21LeftFactorReturnTwoDegree_of_rightFamily hright⟩

/-- Same-degree and succ-degree leaves plus the positive-split subtraction
family leaf give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_xSub
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_rightFamily hsame hsucc
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub hsub)

/-- Right-branch factor-return target for an arbitrary endpoint degree
relation.  The relation is evaluated as `R g.natDegree f.natDegree`, matching
the right branch where `g` is the endpoint with the deleted root. -/
def theorem21RightFactorReturnRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        R g.natDegree f.natDegree →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            Compatible f g

/-- Predicate-restricted right-branch factor-return target for an arbitrary
endpoint degree relation.  The predicate records endpoint side conditions on
`f.natDegree`, the endpoint used by the right branch. -/
def theorem21RightFactorReturnPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        R g.natDegree f.natDegree →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            P f.natDegree → Compatible f g

/-- Predicate-restricted right factor-return relation targets transport along
endpoint predicate implications. -/
theorem theorem21RightFactorReturnPredicateRelationStatement_of_imp
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnPredicateRelationStatement R Q) :
    theorem21RightFactorReturnPredicateRelationStatement R P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact hQ hf hg hsgn hright hdeg hcommon (hPQ _ hfdeg)

/-- The unrestricted right factor-return relation target is the `P := True`
case of the predicate-restricted relation target. -/
theorem theorem21RightFactorReturnPredicateRelation_true_of_relation
    {R : ℕ → ℕ → Prop}
    (hreturn : theorem21RightFactorReturnRelationStatement R) :
    theorem21RightFactorReturnPredicateRelationStatement R
      (fun _ => True) := by
  intro f g r s hf hg hsgn hright hdeg hcommon _
  exact hreturn hf hg hsgn hright hdeg hcommon

/-- A `P := True` right factor-return predicate relation target gives the
unrestricted relation target. -/
theorem theorem21RightFactorReturnRelation_of_predicate_true
    {R : ℕ → ℕ → Prop}
    (hreturn :
      theorem21RightFactorReturnPredicateRelationStatement R
        (fun _ => True)) :
    theorem21RightFactorReturnRelationStatement R := by
  intro f g r s hf hg hsgn hright hdeg hcommon
  exact hreturn hf hg hsgn hright hdeg hcommon trivial

/-- Same-degree right-branch factor-return target. -/
def theorem21RightFactorReturnSameDegreeStatement : Prop :=
  theorem21RightFactorReturnRelationStatement
    (fun m n => m = n)

/-- Succ-degree right-branch factor-return target. -/
def theorem21RightFactorReturnSuccDegreeStatement : Prop :=
  theorem21RightFactorReturnRelationStatement
    (fun m n => m = n + 1)

/-- Two-degree-gap right-branch factor-return target. -/
def theorem21RightFactorReturnTwoDegreeStatement : Prop :=
  theorem21RightFactorReturnRelationStatement
    (fun m n => m = n + 2)

/-- The three right-branch factor-return cases. -/
def theorem21RightFactorReturnDegreeCasesStatement : Prop :=
  theorem21RightFactorReturnSameDegreeStatement ∧
    theorem21RightFactorReturnSuccDegreeStatement ∧
      theorem21RightFactorReturnTwoDegreeStatement

/-- Predicate-restricted same-degree right-branch factor-return target.
The predicate records endpoint side conditions on `f.natDegree`, the endpoint
used by the right branch. -/
def theorem21RightFactorReturnSameDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnPredicateRelationStatement
    (fun m n => m = n) P

/-- Predicate-restricted successor-degree right-branch factor-return target.
The predicate records endpoint side conditions on `f.natDegree`, the endpoint
used by the right branch. -/
def theorem21RightFactorReturnSuccDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnPredicateRelationStatement
    (fun m n => m = n + 1) P

/-- A right all-combinations factor-return leaf for any degree relation gives
the corresponding compatibility factor-return leaf. -/
theorem theorem21RightFactorReturn_of_allComboRelation
    {R : ℕ → ℕ → Prop}
    (hright : theorem21RightFactorReturnAllComboRelationStatement R) :
    theorem21RightFactorReturnRelationStatement R := by
  intro f g r s hf hg hsgn hbranch hdeg hcommon
  exact Compatible.of_allComboRealRooted
    (hright hf hg hsgn hbranch hdeg hcommon)

/-- A same-degree all-combinations right leaf gives the corresponding
compatibility leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_allCombo
    (hright : theorem21RightFactorReturnSameDegreeAllComboStatement) :
    theorem21RightFactorReturnSameDegreeStatement :=
  theorem21RightFactorReturn_of_allComboRelation
    (R := fun m n => m = n) hright

/-- A successor-degree all-combinations right leaf gives the corresponding
compatibility leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_allCombo
    (hright : theorem21RightFactorReturnSuccDegreeAllComboStatement) :
    theorem21RightFactorReturnSuccDegreeStatement :=
  theorem21RightFactorReturn_of_allComboRelation
    (R := fun m n => m = n + 1) hright

/-- A two-degree-gap all-combinations right leaf gives the corresponding
compatibility leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_allCombo
    (hright : theorem21RightFactorReturnTwoDegreeAllComboStatement) :
    theorem21RightFactorReturnTwoDegreeStatement :=
  theorem21RightFactorReturn_of_allComboRelation
    (R := fun m n => m = n + 2) hright

/-- Right all-combinations factor-return degree cases give the corresponding
compatibility degree cases. -/
theorem theorem21RightFactorReturnDegreeCases_of_allComboCases
    (hcases : theorem21RightFactorReturnAllComboDegreeCasesStatement) :
    theorem21RightFactorReturnDegreeCasesStatement :=
  ⟨theorem21RightFactorReturnSameDegree_of_allCombo hcases.1,
    theorem21RightFactorReturnSuccDegree_of_allCombo hcases.2.1,
    theorem21RightFactorReturnTwoDegree_of_allCombo hcases.2.2⟩

/-- Predicate-restricted two-degree-gap right-branch factor-return target.
The predicate records endpoint side conditions on `f.natDegree`, the
lower-degree endpoint in the right branch. -/
def theorem21RightFactorReturnTwoDegreePredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnPredicateRelationStatement
    (fun m n => m = n + 2) P

/-- Predicate-restricted right two-degree factor-return targets transport along
endpoint predicate implications. -/
theorem theorem21RightFactorReturnTwoDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnTwoDegreePredicateStatement Q) :
    theorem21RightFactorReturnTwoDegreePredicateStatement P :=
  theorem21RightFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n + 2) hPQ hQ

/-- Predicate-restricted right same-degree factor-return targets transport
along endpoint predicate implications. -/
theorem theorem21RightFactorReturnSameDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnSameDegreePredicateStatement Q) :
    theorem21RightFactorReturnSameDegreePredicateStatement P :=
  theorem21RightFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n) hPQ hQ

/-- Predicate-restricted right successor-degree factor-return targets
transport along endpoint predicate implications. -/
theorem theorem21RightFactorReturnSuccDegreePredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnSuccDegreePredicateStatement Q) :
    theorem21RightFactorReturnSuccDegreePredicateStatement P :=
  theorem21RightFactorReturnPredicateRelationStatement_of_imp
    (R := fun m n => m = n + 1) hPQ hQ

/-- General symmetry bridge from a left-branch factor-return theorem to the
matching right-branch theorem with the degree relation reversed. -/
theorem theorem21RightFactorReturn_of_leftDegreeRelation
    {R : ℕ → ℕ → Prop}
    (hleft :
      ∀ {p q : ℝ[X]} {a b : ℝ},
        p.Splits → q.Splits → OppositeLeadingSigns p q →
          LeftRootCountBranch p q a b →
            R p.natDegree q.natDegree →
              (∃ k : ℝ[X], Prec (deleteRootFactor p a) k ∧ Prec q k) →
                Compatible p q)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : R g.natDegree f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) :
    Compatible f g :=
  (hleft (p := g) (q := f) (a := s) (b := r)
    hg hf hsgn.symm hright.toLeftBranch_symm hdeg
    (rightDeletionPairCommonInterleaver_symm hcommon)).comm

/-- The right same-degree factor-return case follows from the left same-degree
case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSameDegree_of_leftSameDegree
    (hleft : theorem21LeftFactorReturnSameDegreeStatement) :
    theorem21RightFactorReturnSameDegreeStatement := by
  intro f g r s hf hg hsgn hright hdeg hcommon
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n) hleft hf hg hsgn hright hdeg hcommon

/-- Predicate-restricted same-degree left factor-return targets give the
corresponding right-branch predicate targets by symmetry. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnSameDegreePredicateStatement P) :
    theorem21RightFactorReturnSameDegreePredicateStatement P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n ∧ P n)
    (fun hp hq hsgn' hleft' hrel hcommon' =>
      hleft hp hq hsgn' hleft' hrel.1 hcommon' hrel.2)
    hf hg hsgn hright ⟨hdeg, hfdeg⟩ hcommon

/-- Degree-one-left endpoint package for the right same-degree factor-return
target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_one :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n = 1)
    theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_one

/-- Degree-two-left endpoint package for the right same-degree factor-return
target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_two :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_two

/-- Endpoint cases through left degree two for the right same-degree
factor-return target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_two :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 2)
    theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_two

/-- Degree-three-left endpoint package for the right same-degree factor-return
target, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n = 3)
    (theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_three_of_monic
      hmono)

/-- Degree-three-left endpoint package for the right same-degree factor-return
target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three_of_monic
    xSubQuadraticCubicSplits

/-- Endpoint cases through left degree three for the right same-degree
factor-return target, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 3)
    (theorem21LeftFactorReturnSameDegreePredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Endpoint cases through left degree three for the right same-degree
factor-return target. -/
theorem theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three :
    theorem21RightFactorReturnSameDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three_of_monic
    xSubQuadraticCubicSplits

/-- Degree-one-left endpoint case for the right same-degree factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 1) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right same-degree factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree two for the right same-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 2) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-three-left endpoint case for the right same-degree factor-return leaf,
modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_three_of_monic
    hmono hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-three-left endpoint case for the right same-degree factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegree_of_left_natDegree_three_of_monic
    xSubQuadraticCubicSplits hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree three for the right same-degree
factor-return leaf, modulo the normalized monic quadratic/cubic leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegreePredicate_of_left_natDegree_le_three_of_monic
    hmono hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree three for the right same-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSameDegree_of_left_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 3) :
    Compatible f g :=
  theorem21RightFactorReturnSameDegree_of_left_natDegree_le_three_of_monic
    xSubQuadraticCubicSplits hf hg hsgn hright hdeg hcommon hfdeg

/-- The right successor-degree factor-return case follows from the left
successor-degree case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSuccDegree_of_leftSuccDegree
    (hleft : theorem21LeftFactorReturnSuccDegreeStatement) :
    theorem21RightFactorReturnSuccDegreeStatement := by
  intro f g r s hf hg hsgn hright hdeg hcommon
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n + 1) hleft hf hg hsgn hright hdeg hcommon

/-- Predicate-restricted successor-degree left factor-return targets give the
corresponding right-branch predicate targets by symmetry. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnSuccDegreePredicateStatement P) :
    theorem21RightFactorReturnSuccDegreePredicateStatement P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n + 1 ∧ P n)
    (fun hp hq hsgn' hleft' hrel hcommon' =>
      hleft hp hq hsgn' hleft' hrel.1 hcommon' hrel.2)
    hf hg hsgn hright ⟨hdeg, hfdeg⟩ hcommon

/-- Degree-zero-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_zero :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 0) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 0)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_zero

/-- Degree-one-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_one :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 1)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_one

/-- Low-degree left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_one :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 1) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 1)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_one

/-- Degree-two-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_two :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_two

/-- Endpoint cases through left degree two for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_two :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 2)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_two

/-- Degree-three-left endpoint package for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_three :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n = 3) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n = 3)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_three

/-- Endpoint cases through left degree three for the right successor-degree
factor-return target. -/
theorem theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_three :
    theorem21RightFactorReturnSuccDegreePredicateStatement
      (fun n => n ≤ 3) :=
  theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 3)
    theorem21LeftFactorReturnSuccDegreePredicate_of_right_natDegree_le_three

/-- Degree-zero-left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 0) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_zero
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-one-left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 1) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Low-degree left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 1) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree two for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 2) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-three-left endpoint case for the right successor-degree factor-return
leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 3) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_three
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree three for the right successor-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnSuccDegree_of_left_natDegree_le_three
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 3) :
    Compatible f g :=
  theorem21RightFactorReturnSuccDegreePredicate_of_left_natDegree_le_three
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Predicate-parameterized symmetry bridge for right two-degree factor-return
cases.  The predicate records endpoint restrictions such as degree `0`, degree
`1`, or degree `≤ 1` on the swapped right endpoint. -/
theorem theorem21RightFactorReturnTwoDegree_of_leftPredicate
    {P : ℕ → Prop}
    (hleft :
      ∀ {p q : ℝ[X]} {a b : ℝ},
        p.Splits → q.Splits → OppositeLeadingSigns p q →
          LeftRootCountBranch p q a b →
            p.natDegree = q.natDegree + 2 →
              (∃ k : ℝ[X], Prec (deleteRootFactor p a) k ∧ Prec q k) →
                P q.natDegree → Compatible p q)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : P f.natDegree) :
    Compatible f g :=
  theorem21RightFactorReturn_of_leftDegreeRelation
    (R := fun m n => m = n + 2 ∧ P n)
    (fun hp hq hsgn' hleft' hrel hcommon' =>
      hleft hp hq hsgn' hleft' hrel.1 hcommon' hrel.2)
    hf hg hsgn hright ⟨hdeg, hfdeg⟩ hcommon

/-- Predicate-restricted left two-degree factor-return targets give the
corresponding right-branch predicate targets by symmetry. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnTwoDegreePredicateStatement P) :
    theorem21RightFactorReturnTwoDegreePredicateStatement P := by
  intro f g r s hf hg hsgn hright hdeg hcommon hfdeg
  exact theorem21RightFactorReturnTwoDegree_of_leftPredicate
    hleft hf hg hsgn hright hdeg hcommon hfdeg

/-- A `P := True` right-branch factor-return predicate target gives the
unrestricted right two-degree factor-return target. -/
theorem theorem21RightFactorReturnTwoDegree_of_predicate_true
    (hright :
      theorem21RightFactorReturnTwoDegreePredicateStatement
        (fun _ => True)) :
    theorem21RightFactorReturnTwoDegreeStatement :=
  theorem21RightFactorReturnRelation_of_predicate_true
    (R := fun m n => m = n + 2) hright

/-- The unrestricted right two-degree factor-return target is the `P := True`
case of the predicate-restricted target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_true_of_twoDegree
    (hright : theorem21RightFactorReturnTwoDegreeStatement) :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun _ => True) :=
  theorem21RightFactorReturnPredicateRelation_true_of_relation
    (R := fun m n => m = n + 2) hright

/-- The right two-degree-gap factor-return case follows from the left
two-degree-gap case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnTwoDegree_of_leftTwoDegree
    (hleft : theorem21LeftFactorReturnTwoDegreeStatement) :
    theorem21RightFactorReturnTwoDegreeStatement :=
  theorem21RightFactorReturnTwoDegree_of_predicate_true
    (theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
      (P := fun _ => True)
      (theorem21LeftFactorReturnTwoDegreePredicate_true_of_twoDegree hleft))

/-- Left factor-return degree cases give the matching right cases by symmetry. -/
theorem theorem21RightFactorReturnDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21RightFactorReturnDegreeCasesStatement :=
  ⟨theorem21RightFactorReturnSameDegree_of_leftSameDegree hcases.1,
    theorem21RightFactorReturnSuccDegree_of_leftSuccDegree hcases.2.1,
    theorem21RightFactorReturnTwoDegree_of_leftTwoDegree hcases.2.2⟩

/-- Low-degree left-endpoint cases for the right two-degree factor-return
target, packaged as a predicate-restricted statement. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_one :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 1) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 1)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_one

/-- Constant-left-endpoint package for the right two-degree factor-return
target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_zero :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 0) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 0)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_zero

/-- Degree-one-left-endpoint package for the right two-degree factor-return
target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_one :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 1) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 1)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_one

/-- Endpoint cases through left degree two for the right two-degree
factor-return target, packaged as a predicate-restricted statement. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_two :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n ≤ 2) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n ≤ 2)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_le_two

/-- Degree-two-left endpoint package for the right two-degree factor-return
target, modulo the normalized monic arithmetic leaf. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement) :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    (theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_two_of_monic
      hmono)

/-- Degree-two-left endpoint package for the right two-degree factor-return
target. -/
theorem theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two :
    theorem21RightFactorReturnTwoDegreePredicateStatement
      (fun n => n = 2) :=
  theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate
    (P := fun n => n = 2)
    theorem21LeftFactorReturnTwoDegree_of_right_natDegree_two

/-- Constant-left-endpoint base case for the right two-degree factor-return
leaf, obtained by symmetry from the left constant-right base case. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 0) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_zero
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-one-left-endpoint base case for the right two-degree factor-return
leaf, obtained by symmetry from the left degree-one-right base case. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 1) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Low-degree left-endpoint cases for the right two-degree factor-return
leaf, obtained by symmetry from the left low-degree-right wrapper. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_le_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 1) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_one
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Endpoint cases through left degree two for the right two-degree
factor-return leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_le_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree ≤ 2) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_le_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right two-degree factor-return
leaf, modulo the normalized monic arithmetic leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement)
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two_of_monic
    hmono hf hg hsgn hright hdeg hcommon hfdeg

/-- Degree-two-left endpoint case for the right two-degree factor-return
leaf. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_two
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 2) :
    Compatible f g :=
  theorem21RightFactorReturnTwoDegreePredicate_of_left_natDegree_two
    hf hg hsgn hright hdeg hcommon hfdeg

/-- Predicate-restricted factor-return principle for Liu deletion branches.
The predicate is imposed on the lower-degree endpoint only in the two-degree
branch: on `g.natDegree` in a left branch and on `f.natDegree` in a right
branch. -/
def theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
    (P : ℕ → Prop) : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      (LeftRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
          P g.natDegree → Compatible f g) ∧
      (RightRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
          P f.natDegree → Compatible f g)

/-- Predicate-restricted factor-return principles transport along endpoint
predicate implications. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        Q) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      P := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon hgdeg
    exact (hQ hf hg hsgn).1 hleft hcommon (hPQ _ hgdeg)
  · intro hright hcommon hfdeg
    exact (hQ hf hg hsgn).2 hright hcommon (hPQ _ hfdeg)

/-- Predicate-restricted left factor-return degree cases. -/
def theorem21LeftFactorReturnDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted left factor-return degree cases.  Unlike
`theorem21LeftFactorReturnDegreeCasesPredicateStatement`, the predicate is
available in all three degree branches. -/
def theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreePredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreePredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P

/-- Predicate-restricted right factor-return degree cases. -/
def theorem21RightFactorReturnDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnSameDegreeStatement ∧
    theorem21RightFactorReturnSuccDegreeStatement ∧
      theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted right factor-return degree cases.  Unlike
`theorem21RightFactorReturnDegreeCasesPredicateStatement`, the predicate is
available in all three degree branches. -/
def theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement
    (P : ℕ → Prop) : Prop :=
  theorem21RightFactorReturnSameDegreePredicateStatement P ∧
    theorem21RightFactorReturnSuccDegreePredicateStatement P ∧
      theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Predicate-restricted left and right factor-return degree cases. -/
def theorem21FactorReturnPredicateDegreeCasesStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P ∧
        theorem21RightFactorReturnSameDegreeStatement ∧
          theorem21RightFactorReturnSuccDegreeStatement ∧
            theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Endpoint-predicate-restricted left and right factor-return degree cases. -/
def theorem21EndpointFactorReturnPredicateDegreeCasesStatement
    (P : ℕ → Prop) : Prop :=
  theorem21LeftFactorReturnSameDegreePredicateStatement P ∧
    theorem21LeftFactorReturnSuccDegreePredicateStatement P ∧
      theorem21LeftFactorReturnTwoDegreePredicateStatement P ∧
        theorem21RightFactorReturnSameDegreePredicateStatement P ∧
          theorem21RightFactorReturnSuccDegreePredicateStatement P ∧
            theorem21RightFactorReturnTwoDegreePredicateStatement P

/-- Predicate-restricted left and right factor-return degree cases assemble
into the full six-case package. -/
theorem theorem21FactorReturnPredicateDegreeCases_of_leftRightCases
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnDegreeCasesPredicateStatement P)
    (hright : theorem21RightFactorReturnDegreeCasesPredicateStatement P) :
    theorem21FactorReturnPredicateDegreeCasesStatement P :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

/-- Endpoint-predicate-restricted left and right factor-return degree cases
assemble into the full six-case package. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_leftRightCases
    {P : ℕ → Prop}
    (hleft : theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P)
    (hright :
      theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement P :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

/-- Left projection from a six-case predicate factor-return package. -/
theorem theorem21LeftFactorReturnDegreeCasesPredicate_of_factorCases
    {P : ℕ → Prop}
    (hcases : theorem21FactorReturnPredicateDegreeCasesStatement P) :
    theorem21LeftFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case predicate factor-return package. -/
theorem theorem21RightFactorReturnDegreeCasesPredicate_of_factorCases
    {P : ℕ → Prop}
    (hcases : theorem21FactorReturnPredicateDegreeCasesStatement P) :
    theorem21RightFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

/-- Left projection from a six-case endpoint-predicate factor-return package. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
    {P : ℕ → Prop}
    (hcases : theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case endpoint-predicate factor-return package. -/
theorem theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
    {P : ℕ → Prop}
    (hcases : theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

/-- Predicate-restricted translated compatibility degree cases give
predicate-restricted original left factor-return degree cases. -/
theorem
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedCompatibleCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21LeftFactorReturnSameDegreePredicate_of_translatedCompatiblePredicate
      hcases.1,
    theorem21LeftFactorReturnSuccDegreePredicate_of_translatedCompatiblePredicate
      hcases.2.1,
    theorem21LeftFactorReturnTwoDegreePredicate_of_translatedCompatiblePredicate
      hcases.2.2⟩

/-- Predicate-restricted translated right-family degree cases give
predicate-restricted original left factor-return degree cases. -/
theorem
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedRightFamilyCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedCompatibleCasesPredicate
    (theorem21LeftFactorReturnTranslatedCompatibleCasesPredicate_of_rightFamilyCasesPredicate
      hcases)

/-- Predicate-restricted positive-split x-subtraction degree cases give
predicate-restricted original left factor-return degree cases. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasesPredicate
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21LeftFactorReturnSameDegreePredicate_of_xSubPredicate hrightSucc,
    theorem21LeftFactorReturnSuccDegreePredicate_of_xSubPredicate hsame,
    theorem21LeftFactorReturnTwoDegreePredicate_of_xSubPredicate hleftSucc⟩

/-- Bundled predicate-restricted positive-split x-subtraction cases give
predicate-restricted original left factor-return degree cases. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasesPredicate
    hcases.1 hcases.2.1 hcases.2.2

/-- Predicate-restricted left factor-return case packages transport along
endpoint predicate implications. -/
theorem theorem21LeftFactorReturnDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21LeftFactorReturnDegreeCasesPredicateStatement Q) :
    theorem21LeftFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hQ.1, hQ.2.1,
    theorem21LeftFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Endpoint-predicate-restricted left factor-return case packages transport
along endpoint predicate implications. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement Q) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21LeftFactorReturnSameDegreePredicateStatement_of_imp
      hPQ hQ.1,
    theorem21LeftFactorReturnSuccDegreePredicateStatement_of_imp hPQ hQ.2.1,
    theorem21LeftFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Predicate-restricted right factor-return case packages transport along
endpoint predicate implications. -/
theorem theorem21RightFactorReturnDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21RightFactorReturnDegreeCasesPredicateStatement Q) :
    theorem21RightFactorReturnDegreeCasesPredicateStatement P :=
  ⟨hQ.1, hQ.2.1,
    theorem21RightFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Endpoint-predicate-restricted right factor-return case packages transport
along endpoint predicate implications. -/
theorem theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement Q) :
    theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21RightFactorReturnSameDegreePredicateStatement_of_imp hPQ hQ.1,
    theorem21RightFactorReturnSuccDegreePredicateStatement_of_imp hPQ hQ.2.1,
    theorem21RightFactorReturnTwoDegreePredicateStatement_of_imp hPQ hQ.2.2⟩

/-- Predicate-restricted left/right factor-return case packages transport along
endpoint predicate implications. -/
theorem theorem21FactorReturnPredicateDegreeCasesStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21FactorReturnPredicateDegreeCasesStatement Q) :
    theorem21FactorReturnPredicateDegreeCasesStatement P :=
  theorem21FactorReturnPredicateDegreeCases_of_leftRightCases
    (theorem21LeftFactorReturnDegreeCasesPredicateStatement_of_imp hPQ
      (theorem21LeftFactorReturnDegreeCasesPredicate_of_factorCases hQ))
    (theorem21RightFactorReturnDegreeCasesPredicateStatement_of_imp hPQ
      (theorem21RightFactorReturnDegreeCasesPredicate_of_factorCases hQ))

/-- Endpoint-predicate-restricted left/right factor-return case packages
transport along endpoint predicate implications. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCasesStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ : theorem21EndpointFactorReturnPredicateDegreeCasesStatement Q) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement P :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftRightCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
      hPQ
      (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
        hQ))
    (theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement_of_imp
      hPQ
      (theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
        hQ))

/-- Left endpoint cases through right degree two for all three restored-degree
factor-return branches. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_two :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
      (fun n => n ≤ 2) :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_two

/-- Left endpoint cases through right degree three for all three restored-degree
factor-return branches, modulo the normalized monic quartic/cubic arithmetic
leaf. -/
theorem
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
    (positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
      hmono)

/-- Left endpoint cases through right degree three for all three restored-degree
factor-return branches. -/
theorem theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three :
    theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three_of_monic
    xSubQuarticCubicSplits

/-- Predicate-restricted left factor-return degree cases supply the matching
right cases by symmetry. -/
theorem theorem21RightFactorReturnDegreeCasesPredicate_of_leftCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnDegreeCasesPredicateStatement P) :
    theorem21RightFactorReturnDegreeCasesPredicateStatement P :=
  ⟨theorem21RightFactorReturnSameDegree_of_leftSameDegree hcases.1,
    theorem21RightFactorReturnSuccDegree_of_leftSuccDegree hcases.2.1,
    theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate hcases.2.2⟩

/-- Predicate-restricted left factor-return degree cases supply the matching
right cases by symmetry. -/
theorem theorem21FactorReturnPredicateDegreeCases_of_leftCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnDegreeCasesPredicateStatement P) :
    theorem21FactorReturnPredicateDegreeCasesStatement P :=
  theorem21FactorReturnPredicateDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnDegreeCasesPredicate_of_leftCases hcases)

/-- Endpoint-predicate-restricted left factor-return degree cases supply the
matching right cases by symmetry. -/
theorem theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_leftCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21RightFactorReturnEndpointDegreeCasesPredicateStatement P :=
  ⟨theorem21RightFactorReturnSameDegreePredicate_of_leftPredicate hcases.1,
    theorem21RightFactorReturnSuccDegreePredicate_of_leftPredicate hcases.2.1,
    theorem21RightFactorReturnTwoDegreePredicate_of_leftPredicate hcases.2.2⟩

/-- Endpoint-predicate-restricted left factor-return degree cases supply the
matching right cases by symmetry. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement P :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_leftCases
      hcases)

/-- Full left/right endpoint cases through degree two, with right cases
supplied by symmetry from the named left endpoint package. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_endpoint_le_two :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement
      (fun n => n ≤ 2) :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_two

/-- Full left/right endpoint cases through degree three, modulo the normalized
monic quartic/cubic arithmetic leaf. -/
theorem
    theorem21EndpointFactorReturnPredicateDegreeCases_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement
      (fun n => n ≤ 3) :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three_of_monic
      hmono)

/-- Full left/right endpoint cases through degree three. -/
theorem theorem21EndpointFactorReturnPredicateDegreeCases_of_endpoint_le_three :
    theorem21EndpointFactorReturnPredicateDegreeCasesStatement
      (fun n => n ≤ 3) :=
  theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_right_natDegree_le_three

/-- The predicate-restricted factor-return principle follows from its restored
degree cases. -/
theorem theorem21FactorReturnPredicate_of_degreeCases
    {P : ℕ → Prop}
    (hcases : theorem21FactorReturnPredicateDegreeCasesStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P := by
  let hleftCases :=
    theorem21LeftFactorReturnDegreeCasesPredicate_of_factorCases hcases
  let hrightCases :=
    theorem21RightFactorReturnDegreeCasesPredicate_of_factorCases hcases
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon hgdeg
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleftCases.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.2 hf hg hsgn hleft hdeg hcommon hgdeg
  · intro hright hcommon hfdeg
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hrightCases.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.2 hf hg hsgn hright hdeg hcommon hfdeg

/-- The predicate-restricted factor-return principle follows from endpoint-
predicate-restricted restored degree cases. -/
theorem theorem21FactorReturnPredicate_of_endpointDegreeCases
    {P : ℕ → Prop}
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P := by
  let hleftCases :=
    theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
      hcases
  let hrightCases :=
    theorem21RightFactorReturnEndpointDegreeCasesPredicate_of_endpointFactorCases
      hcases
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon hgdeg
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleftCases.1 hf hg hsgn hleft hdeg hcommon hgdeg
    · exact hleftCases.2.1 hf hg hsgn hleft hdeg hcommon hgdeg
    · exact hleftCases.2.2 hf hg hsgn hleft hdeg hcommon hgdeg
  · intro hright hcommon hfdeg
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hrightCases.1 hf hg hsgn hright hdeg hcommon hfdeg
    · exact hrightCases.2.1 hf hg hsgn hright hdeg hcommon hfdeg
    · exact hrightCases.2.2 hf hg hsgn hright hdeg hcommon hfdeg

/-- It is enough to prove the predicate-restricted left factor-return degree
cases; the right branch is symmetric. -/
theorem theorem21FactorReturnPredicate_of_leftCases
    {P : ℕ → Prop}
    (hcases : theorem21LeftFactorReturnDegreeCasesPredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_degreeCases
    (theorem21FactorReturnPredicateDegreeCases_of_leftCases hcases)

/-- It is enough to prove endpoint-predicate-restricted left factor-return
degree cases; the right branch is symmetric. -/
theorem theorem21FactorReturnPredicate_of_leftEndpointCases
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_endpointDegreeCases
    (theorem21EndpointFactorReturnPredicateDegreeCases_of_leftCases hcases)

/-- Predicate-restricted translated compatibility degree cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_translatedCompatibleCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesPredicateStatement
        P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedCompatibleCasesPredicate
      hcases)

/-- Predicate-restricted translated right-family degree cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_translatedRightFamilyCasesPredicate
    {P : ℕ → Prop}
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesPredicateStatement
        P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_translatedRightFamilyCasesPredicate
      hcases)

/-- Predicate-restricted positive-split x-subtraction degree cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_xSubCasesPredicate
    {P : ℕ → Prop}
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P)
    (hsame :
      positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasesPredicate
      hrightSucc hsame hleftSucc)

/-- Bundled predicate-restricted positive-split x-subtraction cases imply the
predicate-restricted factor-return principle. -/
theorem theorem21FactorReturnPredicate_of_xSubCasePackage
    {P : ℕ → Prop}
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftEndpointCases
    (theorem21LeftFactorReturnEndpointDegreeCasesPredicate_of_xSubCasePackage
      hcases)

/-- A `P := True` restricted factor-return principle gives the unrestricted
factor-return principle. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
        (fun _ => True)) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    exact (hreturn hf hg hsgn).1 hleft hcommon trivial
  · intro hright hcommon
    exact (hreturn hf hg hsgn).2 hright hcommon trivial

/-- The unrestricted factor-return principle proves every predicate-restricted
factor-return principle by forgetting the endpoint predicate. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnPredicate_of_factorReturn
    {P : ℕ → Prop}
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon _hgdeg
    exact (hreturn hf hg hsgn).1 hleft hcommon
  · intro hright hcommon _hfdeg
    exact (hreturn hf hg hsgn).2 hright hcommon

/-- Predicate-`True` factor-return is equivalent to the ordinary factor-return
principle. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnPredicate_true_iff :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun _ => True) ↔
      theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  ⟨theorem21DeletionPairCommonInterleaverFactorReturn_of_predicate_true,
    theorem21DeletionPairCommonInterleaverFactorReturnPredicate_of_factorReturn⟩

/-- Same-degree and succ-degree leaves plus a predicate-restricted two-degree
leaf give the predicate-restricted factor-return route. -/
theorem theorem21FactorReturnPredicate_of_sameSucc_and_twoPredicate
    {P : ℕ → Prop}
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreePredicateStatement P) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement P :=
  theorem21FactorReturnPredicate_of_leftCases ⟨hsame, hsucc, htwo⟩

/-- Current low-endpoint factor-return route: the two-degree branch is proved
whenever the lower-degree endpoint has degree at most two. -/
theorem theorem21FactorReturnPredicate_of_sameSucc_and_endpoint_le_two
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 2) :=
  theorem21FactorReturnPredicate_of_sameSucc_and_twoPredicate
    (P := fun n => n ≤ 2) hsame hsucc
    theorem21LeftFactorReturnTwoDegreePredicate_of_right_natDegree_le_two

/-- Current low-endpoint factor-return route: all three left degree branches
are proved whenever the lower-degree endpoint has degree at most two. -/
theorem theorem21FactorReturnPredicate_of_endpoint_le_two :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 2) :=
  theorem21FactorReturnPredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_two

/-- Conditional low-endpoint factor-return route: once the normalized
quartic/cubic arithmetic terminal is proved, all three left degree branches are
available whenever the lower-degree endpoint has degree at most three. -/
theorem theorem21FactorReturnPredicate_of_endpoint_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21FactorReturnPredicate_of_xSubCasePackage
    (positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three_of_monic
      hmono)

/-- Low-endpoint factor-return route: all three left degree branches are
available whenever the lower-degree endpoint has degree at most three. -/
theorem theorem21FactorReturnPredicate_of_endpoint_le_three :
    theorem21DeletionPairCommonInterleaverFactorReturnPredicateStatement
      (fun n => n ≤ 3) :=
  theorem21FactorReturnPredicate_of_xSubCasePackage
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three

/-- Degree-case split needed to prove the factor-return principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreeStatement ∧
        theorem21RightFactorReturnSameDegreeStatement ∧
          theorem21RightFactorReturnSuccDegreeStatement ∧
            theorem21RightFactorReturnTwoDegreeStatement

/-- Left and right factor-return degree cases assemble into the full six-case
package. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    (hleft : theorem21LeftFactorReturnDegreeCasesStatement)
    (hright : theorem21RightFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  ⟨hleft.1, hleft.2.1, hleft.2.2,
    hright.1, hright.2.1, hright.2.2⟩

/-- Left projection from a six-case ordinary factor-return package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_factorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hcases.1, hcases.2.1, hcases.2.2.1⟩

/-- Right projection from a six-case ordinary factor-return package. -/
theorem theorem21RightFactorReturnDegreeCases_of_factorCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21RightFactorReturnDegreeCasesStatement :=
  ⟨hcases.2.2.2.1, hcases.2.2.2.2.1, hcases.2.2.2.2.2⟩

/-- All-combinations factor-return degree cases give the corresponding
compatibility factor-return degree cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    (theorem21LeftFactorReturnDegreeCases_of_allComboCases
      (theorem21LeftFactorReturnAllComboDegreeCases_of_allComboFactorCases
        hcases))
    (theorem21RightFactorReturnDegreeCases_of_allComboCases
      (theorem21RightFactorReturnAllComboDegreeCases_of_allComboFactorCases
        hcases))

/-- Left factor-return degree cases supply all six left/right cases by
symmetry. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftRightCases
    hcases
    (theorem21RightFactorReturnDegreeCases_of_leftCases hcases)

/-- The explicit factor-return principle follows from its six restored-degree
cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  let hleftCases := theorem21LeftFactorReturnDegreeCases_of_factorCases hcases
  let hrightCases := theorem21RightFactorReturnDegreeCases_of_factorCases hcases
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleftCases.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.1 hf hg hsgn hleft hdeg hcommon
    · exact hleftCases.2.2 hf hg hsgn hleft hdeg hcommon
  · intro hright hcommon
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hrightCases.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.1 hf hg hsgn hright hdeg hcommon
    · exact hrightCases.2.2 hf hg hsgn hright hdeg hcommon

/-- It is enough to prove the left-branch factor-return cases; the right branch
is symmetric. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
      hcases)

/-- All-combinations factor-return degree cases imply the compatibility
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_allComboDegreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_allComboDegreeCases
      hcases)

/-- Left all-combinations factor-return degree cases imply the compatibility
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_allComboCases hcases)

/-- Translated compatibility degree cases imply the factor-return principle
used by the reverse direction. -/
theorem
    theorem21DeletionPairCommonInterleaverFactorReturn_of_translatedCompatibleCases
    (hcases :
      theorem21LeftFactorReturnTranslatedCompatibleDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_translatedCompatibleCases hcases)

/-- Translated right-family degree cases imply the factor-return principle
used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_translatedRightFamilyCases
    (hcases :
      theorem21LeftFactorReturnTranslatedRightFamilyDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_translatedRightFamilyCases
      hcases)

/-- A bundled sign-normalized positive-split x-subtraction case package
implies the factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_xSubCasePackage
      hcases)

/-- Sign-normalized positive-split x-subtraction cases imply the
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCases
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
    ⟨hrightSucc, hsame, hleftSucc⟩

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and a bundled sign-normalized
positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_factorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and a bundled
sign-normalized positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and a bundled
sign-normalized positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCasePackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_factorReturn
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturn_of_xSubCasePackage
      hcases)

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
a bundled sign-normalized positive-split x-subtraction case package. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and sign-normalized positive-split
x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and sign-normalized
positive-split x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCasePackage
    hforward ⟨hrightSucc, hsame, hleftSucc⟩

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant root-count forward direction and
sign-normalized positive-split x-subtraction cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_forward_and_xSubCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hrightSucc :
      positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement)
    (hsame : positiveSplitSameDegreeTranslatedXSubRightFamilyStatement)
    (hleftSucc :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_xSubCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hrightSucc hsame hleftSucc

/-- The factor-return principle follows from same/succ left leaves and the
translated two-degree compatibility target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_translatedTwo
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo
      hsame hsucc htwo)

/-- The factor-return principle follows from same/succ left leaves and the
translated right-family two-degree target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_rightFamily
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_rightFamily
      hsame hsucc hright)

/-- The factor-return principle follows from same/succ left leaves and the
sign-normalized positive-split subtraction-family leaf. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_xSub
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_rightFamily
    hsame hsucc
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub hsub)

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

/-- Bounded Liu Theorem 2.1 package through endpoint degree two.  The forward
direction is the ordinary Liu forward direction, while the reverse direction is
restricted to branch data whose selected lower-degree endpoint has degree at
most two. -/
def theorem21CompatibleRootCountEndpointLeTwoStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g → theorem21RootCountBranches f g) ∧
      (theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g)

/-- Nonconstant bounded Liu Theorem 2.1 package through endpoint degree two.
-/
def theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g → theorem21RootCountBranches f g) ∧
        (theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g)

/-- Bounded Liu Theorem 2.1 package through endpoint degree three.  The forward
direction is the ordinary Liu forward direction, while the reverse direction is
restricted to branch data whose selected lower-degree endpoint has degree at
most three. -/
def theorem21CompatibleRootCountEndpointLeThreeStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g → theorem21RootCountBranches f g) ∧
      (theorem21RootCountBranchesEndpointLeThree f g → Compatible f g)

/-- Nonconstant bounded Liu Theorem 2.1 package through endpoint degree three.
-/
def theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g → theorem21RootCountBranches f g) ∧
        (theorem21RootCountBranchesEndpointLeThree f g → Compatible f g)

/-- Low-degree Liu Theorem 2.1 package through endpoint degree three, stated
with the ordinary branch predicate and explicit endpoint degree bounds. -/
def theorem21CompatibleRootCountNatDegreeLeThreeStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≤ 3 → g.natDegree ≤ 3 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant low-degree Liu Theorem 2.1 package through endpoint degree
three, stated with the ordinary branch predicate and explicit endpoint degree
bounds. -/
def theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 3 → g.natDegree ≤ 3 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Low-degree Liu Theorem 2.1 package through endpoint degree two, stated
with the ordinary branch predicate and explicit endpoint degree bounds. -/
def theorem21CompatibleRootCountNatDegreeLeTwoStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≤ 2 → g.natDegree ≤ 2 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant low-degree Liu Theorem 2.1 package through endpoint degree
two, stated with the ordinary branch predicate and explicit endpoint degree
bounds. -/
def theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant no-common-root low-degree Liu Theorem 2.1 package through
endpoint degree two. -/
def theorem21CompatibleRootCountNatDegreeLeTwoNoCommonNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant no-common-root low-degree forward direction through endpoint
degree two. -/
def theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        Compatible f g → theorem21RootCountBranches f g

/-- Corrected nonconstant low-degree Liu package through endpoint degree two,
using an explicit common-root deletion branch in the conclusion. -/
def theorem21CompatibleRootCountWithCommonNatDegreeLeTwoNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        (Compatible f g ↔ theorem21RootCountBranchesWithCommon f g)

/-- Corrected nonconstant low-degree forward direction through endpoint degree
two, with an explicit common-root deletion branch. -/
def
    theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 2 → g.natDegree ≤ 2 →
        Compatible f g → theorem21RootCountBranchesWithCommon f g

/-- Nonconstant linear-endpoint Liu Theorem 2.1 package.  This is a checked
base case for the forward direction together with the existing low-degree
reverse route. -/
def theorem21CompatibleRootCountNatDegreeLeOneNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 1 → g.natDegree ≤ 1 →
        (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Isolated nonconstant linear-endpoint forward direction of Liu Theorem 2.1.
The compatibility hypothesis is retained for theorem-shape compatibility, but
the branch condition follows from the endpoint degree bounds. -/
def theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 1 → g.natDegree ≤ 1 →
        Compatible f g → theorem21RootCountBranches f g

/-- The nonconstant linear-endpoint forward direction is checked directly by
deleting the unique largest root on the side selected by the largest-root
comparison. -/
theorem theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstant :
    theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat
  exact theorem21RootCountBranches_of_compatible_natDegree_le_one_nonconstant
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat

/-- Isolated nonconstant linear-endpoint forward direction, restated with
branch-retaining deletion-pair common-interleaver witnesses. -/
def theorem21CompatibleToDeletionPairCommonInterleaverBranchesNatDegreeLeOneNonconstantStatement :
    Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 1 → g.natDegree ≤ 1 →
        Compatible f g → theorem21DeletionPairCommonInterleaverBranches f g

/-- The checked nonconstant linear-endpoint forward branch supplies the
branch-retaining deletion-pair common-interleaver package. -/
theorem theorem21CompatibleToDeletionPairCommonInterleaverBranchesNatDegreeLeOneNonconstant :
    theorem21CompatibleToDeletionPairCommonInterleaverBranchesNatDegreeLeOneNonconstantStatement :=
  by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat
  exact theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
    hf hg hsgn
    (theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstant
      f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hcompat)

/-- The nonconstant linear-endpoint case of Liu Theorem 2.1 is fully checked:
the forward branch condition follows by root counting after deleting the
unique largest root, and the reverse implication is the existing degree-three
reverse route. -/
theorem theorem21CompatibleRootCountNatDegreeLeOneNonconstant :
    theorem21CompatibleRootCountNatDegreeLeOneNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  constructor
  · exact theorem21CompatibleToRootCountBranchesNatDegreeLeOneNonconstant
      f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  · intro hbranches
    exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_three
      hf hg hsgn hfdeg_ne hgdeg_ne
      (hfdeg_le.trans (by norm_num)) (hgdeg_le.trans (by norm_num))
      hbranches

/-- Low-degree bounded Liu equivalence through endpoint degree two, assuming
the isolated forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwo_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  constructor
  · exact hforward hf hg hsgn
  · intro hbranches
    exact theorem21RootCountBranchesToCompatible_of_natDegree_le_two
      hf hg hsgn hfdeg hgdeg hbranches

/-- Nonconstant low-degree bounded Liu equivalence through endpoint degree
two, assuming the isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact hforward hf hg hsgn hfdeg_ne hgdeg_ne
  · intro hbranches
    exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_two
      hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hbranches

/-- The nonconstant no-common-root low-degree forward direction through
endpoint degree two is checked directly. -/
theorem theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstant :
    theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstantStatement :=
  by
  intro f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg hcompat
  exact theorem21RootCountBranches_of_compatible_natDegree_le_two_of_no_common
    hf hg hsgn hcompat hno hfdeg_ne hgdeg_ne hfdeg hgdeg

/-- The nonconstant no-common-root low-degree Liu equivalence through endpoint
degree two is fully checked. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNoCommonNonconstant :
    theorem21CompatibleRootCountNatDegreeLeTwoNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact
      theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstant
        f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg
  · intro hbranches
    exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_two
      hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hbranches

/-- The corrected nonconstant low-degree forward direction through endpoint
degree two follows from the no-common forward theorem and the automatic
common-root deletion branch. -/
theorem
    theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstant :
    theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstantStatement :=
  by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hcompat
  by_cases hno : NoCommonRoots f g
  · exact Or.inl
      (theorem21CompatibleToRootCountBranchesNatDegreeLeTwoNoCommonNonconstant
        f g hf hg hsgn hno hfdeg_ne hgdeg_ne hfdeg hgdeg hcompat)
  · have hcommon : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r := by
      by_contra hmissing
      exact hno (by
        intro r hfr hgr
        exact hmissing ⟨r, hfr, hgr⟩)
    rcases hcommon with ⟨r, hfr, hgr⟩
    exact Or.inr
      ⟨r, hfr, hgr,
        compatible_deleteRootFactor_of_common_root hcompat hfr hgr⟩

/-- The corrected nonconstant low-degree Liu equivalence through endpoint
degree two is fully checked, with common roots handled by an explicit deletion
branch. -/
theorem theorem21CompatibleRootCountWithCommonNatDegreeLeTwoNonconstant :
    theorem21CompatibleRootCountWithCommonNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact
      theorem21CompatibleToRootCountBranchesWithCommonNatDegreeLeTwoNonconstant
        f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  · intro hbranches
    rcases hbranches with hbranches | hcommon
    · exact theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_two
        hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg hbranches
    · exact CommonRootDeletionCompatibleBranch.compatible hcommon

/-- Reassemble the bounded endpoint-degree-two theorem package from the full
forward direction and the bounded endpoint-degree-two reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeTwoStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Current bounded endpoint-degree-two Liu package, assuming the isolated
forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_reverse
    hforward theorem21RootCountBranchesToCompatible_of_endpoint_le_two

/-- Reassemble the bounded endpoint-degree-two theorem package from the
branch-retaining common-interleaver forward direction and a
predicate-restricted reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranches_of_commonForward hforward)
    (fun hf hg hsgn hbranches => hreverse hf hg hsgn hbranches)

/-- Reassemble the bounded endpoint-degree-two theorem package from the full
forward direction and a predicate-restricted reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreverse

/-- Current bounded endpoint-degree-two Liu package from endpoint
factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_endpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)

/-- Current bounded endpoint-degree-two Liu package from endpoint
factor-return case packages and the full root-count forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_endpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)

/-- Current bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases and the full root-count forward
direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current bounded endpoint-degree-two Liu package, assuming the isolated
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwo_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeTwoStatement :=
  theorem21CompatibleRootCountEndpointLeTwo_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_two

/-- Reassemble the nonconstant bounded endpoint-degree-two theorem package
from the nonconstant forward direction and the bounded endpoint-degree-two
reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          f.natDegree ≠ 0 → g.natDegree ≠ 0 →
            theorem21RootCountBranchesEndpointLeTwo f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne
  exact ⟨hforward hf hg hsgn hfdeg_ne hgdeg_ne,
    hreverse hf hg hsgn hfdeg_ne hgdeg_ne⟩

/-- Current nonconstant bounded endpoint-degree-two Liu package, assuming the
isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_reverse
    hforward theorem21RootCountBranchesToCompatibleNonconstant_of_endpoint_le_two

/-- Reassemble the nonconstant bounded endpoint-degree-two theorem package
from the branch-retaining common-interleaver forward direction and a
predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesNonconstant_of_commonForward
      hforward)
    (fun hf hg hsgn hfdeg_ne hgdeg_ne hbranches =>
      hreverse hf hg hsgn hfdeg_ne hgdeg_ne hbranches)

/-- Reassemble the nonconstant bounded endpoint-degree-two theorem package
from the nonconstant forward direction and a predicate-restricted reverse
direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreverse

/-- Current nonconstant bounded endpoint-degree-two Liu package from endpoint
factor-return case packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_endpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)

/-- Current nonconstant bounded endpoint-degree-two Liu package from endpoint
factor-return case packages and the nonconstant root-count forward direction.
-/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_endpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_xSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)

/-- Current nonconstant bounded endpoint-degree-two Liu package from bundled
predicate-restricted x-subtraction cases and the nonconstant root-count forward
direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 2)) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant bounded endpoint-degree-two Liu package, assuming the
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_two

/-- The bounded endpoint-degree-two package restricts to the ordinary
low-degree statement with explicit endpoint degree bounds. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwo_of_endpointLeTwo
    (h : theorem21CompatibleRootCountEndpointLeTwoStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn).1
  · intro hbranches
    exact (h f g hf hg hsgn).2
      (theorem21RootCountBranchesEndpointLeTwo_of_natDegree_le_two
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-two package restricts to its nonconstant
endpoint-degree-two form. -/
theorem theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_endpointLeTwo
    (h : theorem21CompatibleRootCountEndpointLeTwoStatement) :
    theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne
  exact h f g hf hg hsgn

/-- The ordinary endpoint-degree-two Liu package restricts to its nonconstant
form. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_natDegreeLeTwo
    (h : theorem21CompatibleRootCountNatDegreeLeTwoStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne hfdeg hgdeg
  exact h f g hf hg hsgn hfdeg hgdeg

/-- The nonconstant bounded endpoint-degree-two package restricts to the
ordinary nonconstant low-degree statement with explicit endpoint degree bounds.
-/
theorem
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_endpointLeTwoNonconstant
    (h : theorem21CompatibleRootCountEndpointLeTwoNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).1
  · intro hbranches
    exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).2
      (theorem21RootCountBranchesEndpointLeTwo_of_natDegree_le_two
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-two package restricts directly to the
ordinary nonconstant low-degree statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_endpointLeTwo
    (h : theorem21CompatibleRootCountEndpointLeTwoStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_natDegreeLeTwo
    (theorem21CompatibleRootCountNatDegreeLeTwo_of_endpointLeTwo h)

/-- Current low-degree endpoint-two Liu theorem package from a
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwo_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoStatement :=
  theorem21CompatibleRootCountNatDegreeLeTwo_of_endpointLeTwo
    (theorem21CompatibleRootCountEndpointLeTwo_of_commonForward hforward)

/-- Current nonconstant low-degree endpoint-two Liu theorem package from a
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeTwoNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeTwoNonconstant_of_endpointLeTwoNonconstant
    (theorem21CompatibleRootCountEndpointLeTwoNonconstant_of_commonForward
      hforward)

/-- The bounded endpoint-degree-three package restricts to the ordinary
low-degree statement with explicit endpoint degree bounds. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_endpointLeThree
    (h : theorem21CompatibleRootCountEndpointLeThreeStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn).1
  · intro hbranches
    exact (h f g hf hg hsgn).2
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-three package restricts to the nonconstant
bounded endpoint-degree-three package. -/
theorem theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_endpointLeThree
    (h : theorem21CompatibleRootCountEndpointLeThreeStatement) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne
  exact h f g hf hg hsgn

/-- The ordinary low-degree Liu package restricts to its nonconstant form. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_natDegreeLeThree
    (h : theorem21CompatibleRootCountNatDegreeLeThreeStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn _hfdeg_ne _hgdeg_ne hfdeg hgdeg
  exact h f g hf hg hsgn hfdeg hgdeg

/-- The bounded endpoint-degree-three nonconstant package restricts to the
ordinary nonconstant low-degree statement with explicit endpoint degree bounds.
-/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_endpointLeThreeNonconstant
    (h : theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg hgdeg
  constructor
  · exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).1
  · intro hbranches
    exact (h f g hf hg hsgn hfdeg_ne hgdeg_ne).2
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- The bounded endpoint-degree-three package restricts directly to the
ordinary nonconstant low-degree statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_endpointLeThree
    (h : theorem21CompatibleRootCountEndpointLeThreeStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_natDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThree_of_endpointLeThree h)

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and the bounded reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          theorem21RootCountBranchesEndpointLeThree f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeThreeStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Reassemble the bounded endpoint-degree-three theorem package from the
branch-retaining common-interleaver forward direction and a
predicate-restricted reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranches_of_commonForward hforward)
    (fun hf hg hsgn hbranches => hreverse hf hg hsgn hbranches)

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and a predicate-restricted reverse direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hreverse

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and endpoint factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)

/-- Reassemble the bounded endpoint-degree-three theorem package from the
full root-count forward direction and endpoint factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_endpointDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and left endpoint factor-return case packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_leftEndpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
      hcases)

/-- Reassemble the bounded endpoint-degree-three theorem package from the
full root-count forward direction and left endpoint factor-return case
packages. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_leftEndpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Reassemble the bounded endpoint-degree-three theorem package from the full
forward direction and bundled predicate-restricted x-subtraction cases. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)

/-- Reassemble the bounded endpoint-degree-three theorem package from the
full root-count forward direction and bundled predicate-restricted
x-subtraction cases. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current bounded endpoint-degree-three Liu package, assuming the isolated
forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three

/-- Current bounded endpoint-degree-three Liu package, assuming the isolated
branch-retaining common-interleaver forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeThree_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountEndpointLeThreeStatement :=
  theorem21CompatibleRootCountEndpointLeThree_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three

/-- Low-degree bounded Liu equivalence with the ordinary branch statement.
The reverse direction uses the endpoint-degree-three route after converting
ordinary branch data using the explicit degree bounds. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  ⟨hforward hf hg hsgn,
    theorem21RootCountBranchesToCompatible_of_natDegree_le_three
      hf hg hsgn hfdeg hgdeg⟩

/-- Low-degree bounded Liu equivalence from a predicate-restricted reverse
direction, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · exact hforward hf hg hsgn
  · intro hbranches
    exact hreverse hf hg hsgn
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- Low-degree bounded Liu equivalence from the branch-retaining
common-interleaver forward direction and a predicate-restricted reverse
direction. -/
theorem
    theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · intro hcompat
    exact theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
      (hforward hf hg hsgn hcompat)
  · intro hbranches
    exact hreverse hf hg hsgn
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg hgdeg hbranches)

/-- Low-degree bounded Liu equivalence from endpoint factor-return case
packages, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeEndpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)
    hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from endpoint factor-return case
packages and the root-count forward direction, with the ordinary branch
statement. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeEndpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from left endpoint factor-return case
packages, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeLeftCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
      hcases)
    hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from left endpoint factor-return case
packages and the root-count forward direction, with right cases supplied by
symmetry. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeLeftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from bundled predicate-restricted
x-subtraction cases, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeXSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)
    hf hg hsgn hfdeg hgdeg

/-- Low-degree bounded Liu equivalence from bundled predicate-restricted
x-subtraction cases and the root-count forward direction, with the ordinary
branch statement. -/
theorem theorem21CompatibleRootCount_of_forward_and_natDegree_le_three_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCount_of_commonForward_and_natDegreeLeThreeXSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases hf hg hsgn hfdeg hgdeg

/-- Reassemble the low-degree Liu theorem package from the full forward
direction and a predicate-restricted reverse direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  exact
    theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
      (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
        hforward)
      hreverse hf hg hsgn hfdeg hgdeg

/-- Reassemble the low-degree Liu theorem package from the branch-retaining
common-interleaver forward direction and a predicate-restricted reverse
direction. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg
  exact
    theorem21CompatibleRootCount_of_commonForward_and_natDegree_le_three_predicateReverse
      hforward hreverse hf hg hsgn hfdeg hgdeg

/-- Current low-degree Liu theorem package with the ordinary branch statement,
assuming the isolated forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three

/-- Current low-degree Liu theorem package with the ordinary branch statement,
assuming the isolated branch-retaining common-interleaver forward direction.
-/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicate_of_endpoint_le_three

/-- Current low-degree Liu theorem package from endpoint factor-return case
packages, with the ordinary branch statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_endpointCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_endpointDegreeCases
      hcases)

/-- Current low-degree Liu theorem package from endpoint factor-return case
packages and the root-count forward direction, with the ordinary branch
statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current low-degree Liu theorem package from left endpoint factor-return case
packages, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_leftCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_leftEndpointCases
      hcases)

/-- Current low-degree Liu theorem package from left endpoint factor-return
case packages and the root-count forward direction, with right cases supplied
by symmetry. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_leftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Current low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases, with the ordinary branch statement.
-/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_xSubCasePackage
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicate_of_xSubCasePackage
      hcases)

/-- Current low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases and the root-count forward direction,
with the ordinary branch statement. -/
theorem theorem21CompatibleRootCountNatDegreeLeThree_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeStatement :=
  theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward_and_xSubCasePackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and bounded nonconstant reverse
direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      ∀ {f g : ℝ[X]},
        f.Splits → g.Splits → OppositeLeadingSigns f g →
          f.natDegree ≠ 0 → g.natDegree ≠ 0 →
            theorem21RootCountBranchesEndpointLeThree f g → Compatible f g) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact ⟨hforward hf hg hsgn hf_deg hg_deg,
    hreverse hf hg hsgn hf_deg hg_deg⟩

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant branch-retaining common-interleaver forward direction and
a predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesNonconstant_of_commonForward
      hforward)
    (fun hf hg hsgn hf_deg hg_deg hbranches =>
      hreverse hf hg hsgn hf_deg hg_deg hbranches)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and a predicate-restricted nonconstant
reverse direction. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hreverse

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and endpoint factor-return case
packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_endpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant root-count forward direction and endpoint factor-return
case packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and left endpoint factor-return case
packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_leftCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
      hcases)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant root-count forward direction and left endpoint
factor-return case packages. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_leftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant forward direction and bundled predicate-restricted
x-subtraction cases. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_xSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)

/-- Reassemble the nonconstant bounded endpoint-degree-three theorem package
from the nonconstant root-count forward direction and bundled
predicate-restricted x-subtraction cases. -/
theorem
    theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant bounded endpoint-degree-three Liu package, assuming the
isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicate_of_endpoint_le_three

/-- Current nonconstant bounded endpoint-degree-three Liu package, assuming
the isolated nonconstant branch-retaining common-interleaver forward direction.
-/
theorem theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountEndpointLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountEndpointLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three

/-- Low-degree nonconstant bounded Liu equivalence with the ordinary branch
statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  ⟨hforward hf hg hsgn hfdeg_ne hgdeg_ne,
    theorem21RootCountBranchesToCompatibleNonconstant_of_natDegree_le_three
      hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le⟩

/-- Low-degree nonconstant bounded Liu equivalence from a
predicate-restricted nonconstant reverse direction, with the ordinary branch
statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · exact hforward hf hg hsgn hfdeg_ne hgdeg_ne
  · intro hbranches
    exact hreverse hf hg hsgn hfdeg_ne hgdeg_ne
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg_le hgdeg_le hbranches)

/-- Low-degree nonconstant bounded Liu equivalence from the nonconstant
branch-retaining common-interleaver forward direction and a
predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g := by
  constructor
  · intro hcompat
    exact theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
      (hforward hf hg hsgn hfdeg_ne hgdeg_ne hcompat)
  · intro hbranches
    exact hreverse hf hg hsgn hfdeg_ne hgdeg_ne
      (theorem21RootCountBranchesEndpointLeThree_of_natDegree_le_three
        hfdeg_le hgdeg_le hbranches)

/-- Low-degree nonconstant bounded Liu equivalence from endpoint factor-return
case packages, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeEndpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from endpoint factor-return
case packages and the nonconstant root-count forward direction, with the
ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeEndpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from left endpoint
factor-return case packages, with right cases supplied by symmetry. -/
theorem theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeLeftCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
      hcases)
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from left endpoint
factor-return case packages and the nonconstant root-count forward direction,
with right cases supplied by symmetry. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeLeftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from bundled
predicate-restricted x-subtraction cases, with the ordinary branch statement.
-/
theorem
    theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeXSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)
    hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Low-degree nonconstant bounded Liu equivalence from bundled
predicate-restricted x-subtraction cases and the nonconstant root-count forward
direction, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNonconstant_of_forward_and_natDegree_le_three_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3))
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  theorem21CompatibleRootCountNonconstant_of_commonForward_natDegreeLeThreeXSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Reassemble the nonconstant low-degree Liu theorem package from the
nonconstant forward direction and a predicate-restricted nonconstant reverse
direction. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_predicateReverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  exact
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
      (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
        hforward)
      hreverse hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Reassemble the nonconstant low-degree Liu theorem package from the
nonconstant branch-retaining common-interleaver forward direction and a
predicate-restricted nonconstant reverse direction. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hreverse :
      theorem21RootCountBranchesToCompatiblePredicateNonconstantStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le
  exact
    theorem21CompatibleRootCountNonconstant_of_commonForward_and_natDegree_le_three_predicateReverse
      hforward hreverse hf hg hsgn hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le

/-- Current nonconstant low-degree Liu theorem package with the ordinary branch
statement, assuming the isolated nonconstant forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three

/-- Current nonconstant low-degree Liu theorem package with the ordinary branch
statement, assuming the isolated nonconstant branch-retaining common-interleaver
forward direction. -/
theorem theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpoint_le_three

/-- Current nonconstant low-degree Liu theorem package from endpoint
factor-return case packages, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_endpointCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_endpointDegreeCases
      hcases)

/-- Current nonconstant low-degree Liu theorem package from endpoint
factor-return case packages and the nonconstant root-count forward direction,
with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_endpointDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21EndpointFactorReturnPredicateDegreeCasesStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_endpointCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant low-degree Liu theorem package from left endpoint
factor-return case packages, with right cases supplied by symmetry. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_leftCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_leftEndpointCases
      hcases)

/-- Current nonconstant low-degree Liu theorem package from left endpoint
factor-return case packages and the nonconstant root-count forward direction,
with right cases supplied by symmetry. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_leftEndpointCases
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      theorem21LeftFactorReturnEndpointDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_leftCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

/-- Current nonconstant low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases, with the ordinary branch statement.
-/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_xSubPackage
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_predicateReverse
    hforward
    (theorem21RootCountBranchesToCompatiblePredicateNonconstant_of_xSubCasePackage
      hcases)

/-- Current nonconstant low-degree Liu theorem package from bundled
predicate-restricted x-subtraction cases and the nonconstant root-count forward
direction, with the ordinary branch statement. -/
theorem
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward_and_xSubCasePackage
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hcases :
      positiveSplitTranslatedXSubRightFamilyDegreeCasesPredicateStatement
        (fun n => n ≤ 3)) :
    theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement :=
  theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward_and_xSubPackage
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hcases

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

/-- Normalized deletion-pair compatibility data obtained from Liu branch data.
The four leaves match the four possible positive-leading normalizations of the
left/right deletion branches. -/
def theorem21PositiveDeletionCompatibleBranches (f g : ℝ[X]) : Prop :=
  ∃ r s,
    (Compatible (deleteRootFactor f r) (-g) ∨
        Compatible (-(deleteRootFactor f r)) g) ∨
      (Compatible f (-(deleteRootFactor g s)) ∨
        Compatible (-f) (deleteRootFactor g s))

/-- Branch-retaining common-interleaver data imply the corresponding
normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (h : theorem21DeletionPairCommonInterleaverBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl
      (hleft.1.positiveDeletionPair_compatible_of_commonInterleaver
        hsgn hleft.2)⟩
  · exact ⟨r, s, Or.inr
      (hright.1.positiveDeletionPair_compatible_of_commonInterleaver
        hsgn hright.2)⟩

/-- Positive deletion root-count branches imply the corresponding normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_positiveDeletionCountBranches
    {f g : ℝ[X]} (h : theorem21PositiveDeletionCountBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · rcases hleft with hfg | hfg
    · exact ⟨r, s, Or.inl (Or.inl hfg.compatible)⟩
    · exact ⟨r, s, Or.inl (Or.inr hfg.compatible)⟩
  · rcases hright with hfg | hfg
    · exact ⟨r, s, Or.inr (Or.inl hfg.compatible)⟩
    · exact ⟨r, s, Or.inr (Or.inr hfg.compatible)⟩

/-- Liu root-count branches imply normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    hsgn (theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
      hf_splits hg_splits hsgn h)

/-- Projection form of the isolated branch-retaining deletion-pair
common-interleaver forward direction. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  hforward hf hg hsgn hcompat

/-- Projection form of the isolated nonconstant branch-retaining deletion-pair
common-interleaver forward direction. -/
theorem
    theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward_nonconstant
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  hforward hf hg hsgn hf_deg hg_deg hcompat

/-- The isolated branch-retaining deletion-pair common-interleaver forward
direction supplies normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    hsgn
    (theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward
      hforward hf hg hsgn hcompat)

/-- The isolated nonconstant branch-retaining deletion-pair common-interleaver
forward direction supplies normalized deletion compatibility branches. -/
theorem
    theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward_nonconstant
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    hsgn
    (theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward_nonconstant
      hforward hf hg hsgn hf_deg hg_deg hcompat)

/-- The isolated forward direction of Liu Theorem 2.1 supplies normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hf hg hsgn hcompat

/-- The isolated nonconstant forward direction of Liu Theorem 2.1 supplies
normalized deletion compatibility branches. -/
theorem
    theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_commonForward_nonconstant
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The forward direction of Liu Theorem 2.1 supplies normalized deletion
compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- The nonconstant forward direction of Liu Theorem 2.1 supplies normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The isolated forward direction of Liu Theorem 2.1 supplies
branch-retaining common interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hf hg hsgn hcompat

/-- The isolated nonconstant forward direction of Liu Theorem 2.1 supplies
branch-retaining common interleaver witnesses for the actual deletion pair. -/
theorem
    theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_commonForward_nonconstant
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)
    hf hg hsgn hf_deg hg_deg hcompat

/-- The forward direction of Liu Theorem 2.1 supplies branch-retaining common
interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- The nonconstant forward direction of Liu Theorem 2.1 supplies
branch-retaining common interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Liu Theorem 2.1, restated with branch-retaining deletion-pair
common-interleaver witnesses. -/
theorem compatible_iff_theorem21DeletionPairCommonInterleaverBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g :=
  (theorem21DeletionPairCommonInterleaverIff_of_theorem21CompatibleRootCount
    h) f g hf hg hsgn

/-- The nonconstant Liu Theorem 2.1 statement, restated with branch-retaining
deletion-pair common-interleaver witnesses. -/
theorem compatible_iff_theorem21DeletionPairCommonInterleaverBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g :=
  (theorem21DeletionPairCommonInterleaverIffNonconstant_of_theorem21CompatibleRootCount
    h) f g hf hg hsgn hf_deg hg_deg

/-- Same-degree common-interleaver endpoint from the Liu-side positive-split
root-count leaf. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount
    (hpack : positiveSplitSameDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno)
    |>.pairHasCommonInterleaver_of_sameDegree hdeg

/-- Succ-degree common-interleaver endpoint from the Liu-side positive-split
root-count leaf. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount
    (hpack : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity
      hf_pos hg_pos hfnn hgnn hfg hdeg
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)
    |>.pairHasCommonInterleaver_of_succDegree hdeg

/-- The two positive-split root-count leaves supply the existing
positive-leading compatibility-to-common-interleaver bridge. -/
theorem
    compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    (hsame : positiveSplitSameDegreeRootCountAboveNonRootStatement)
    (hsucc : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (sameDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount hsame)
    (succDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount hsucc)

/-- The strict-upper non-root count leaves also route through the
positive-split package before reaching the common-interleaver endpoint. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot_via_positiveSplit
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    (positiveSplitSameDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot hsame)
    (positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot hsucc)

/-- The checked same-degree analytic count spine and the succ-degree
common-left-interleaver reduction supply the compatible-pair endpoint. -/
theorem
    compatiblePairHasCommonInterleaver_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
    (hsucc : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    positiveSplitSameDegreeRootCountAboveNonRoot_from_analytic
    (positiveSplitSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver
      hsucc)

/-- Finite-family Chudnovsky--Seymour package from the Liu-side
positive-split root-count leaves. -/
theorem chudnovskySeymour_fourWay_of_positiveSplitRootCountAboveNonRoot
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : positiveSplitSameDegreeRootCountAboveNonRootStatement)
    (hsucc : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos (fs := fs) hrr hpos
    (compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
      hsame hsucc)

/-- Finite-family Chudnovsky--Seymour package from the checked same-degree
analytic spine and the succ-degree common-left-interleaver reduction. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsucc : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos (fs := fs) hrr hpos
    (compatiblePairHasCommonInterleaver_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
      hsucc)

/-- Liu Corollary 2.2: compatible real-rooted polynomials with opposite leading
signs have degree gap at most two. -/
def corollary22DegreeDiffStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Nonconstant form of Liu Corollary 2.2. -/
def corollary22DegreeDiffNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Low-degree form of Liu Corollary 2.2 through endpoint degree three. -/
def corollary22DegreeDiffNatDegreeLeThreeStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≤ 3 → g.natDegree ≤ 3 →
      Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Nonconstant low-degree form of Liu Corollary 2.2 through endpoint degree
three. -/
def corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      f.natDegree ≤ 3 → g.natDegree ≤ 3 →
        Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Projection form of `corollary22DegreeDiffStatement`. -/
theorem corollary22DegreeDiff
    (h : corollary22DegreeDiffStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hcompat

/-- Projection form of `corollary22DegreeDiffNonconstantStatement`. -/
theorem corollary22DegreeDiff_nonconstant
    (h : corollary22DegreeDiffNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hf_deg hg_deg hcompat

/-- Projection form of `corollary22DegreeDiffNatDegreeLeThreeStatement`. -/
theorem corollary22DegreeDiff_natDegree_le_three
    (h : corollary22DegreeDiffNatDegreeLeThreeStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hfdeg hgdeg hcompat

/-- Projection form of
`corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement`. -/
theorem corollary22DegreeDiff_natDegree_le_three_nonconstant
    (h : corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hfdeg : f.natDegree ≤ 3) (hgdeg : g.natDegree ≤ 3)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hf_deg hg_deg hfdeg hgdeg hcompat

/-- Low-degree Liu Corollary 2.2 follows from the checked low-degree
Theorem 2.1 package. -/
theorem corollary22DegreeDiffNatDegreeLeThree_of_theorem21NatDegreeLeThree
    (h : theorem21CompatibleRootCountNatDegreeLeThreeStatement) :
    corollary22DegreeDiffNatDegreeLeThreeStatement := by
  intro f g hf hg hsgn hfdeg hgdeg hcompat
  exact natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
    ((h f g hf hg hsgn hfdeg hgdeg).1 hcompat)

/-- Nonconstant low-degree Liu Corollary 2.2 follows from the checked
nonconstant low-degree Theorem 2.1 package. -/
theorem
    corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_theorem21NatDegreeLeThree
    (h : theorem21CompatibleRootCountNatDegreeLeThreeNonconstantStatement) :
    corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg hfdeg hgdeg hcompat
  exact natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
    ((h f g hf hg hsgn hf_deg hg_deg hfdeg hgdeg).1 hcompat)

/-- Low-degree Liu Corollary 2.2 follows from the isolated branch-retaining
common-interleaver forward direction. -/
theorem corollary22DegreeDiffNatDegreeLeThree_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    corollary22DegreeDiffNatDegreeLeThreeStatement :=
  corollary22DegreeDiffNatDegreeLeThree_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThree_of_commonForward hforward)

/-- Nonconstant low-degree Liu Corollary 2.2 follows from the isolated
nonconstant branch-retaining common-interleaver forward direction. -/
theorem corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement :=
  corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_commonForward
      hforward)

/-- Low-degree Liu Corollary 2.2 follows from the isolated forward direction of
Theorem 2.1. -/
theorem corollary22DegreeDiffNatDegreeLeThree_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    corollary22DegreeDiffNatDegreeLeThreeStatement :=
  corollary22DegreeDiffNatDegreeLeThree_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThree_of_forward hforward)

/-- Nonconstant low-degree Liu Corollary 2.2 follows from the isolated
nonconstant forward direction of Theorem 2.1. -/
theorem corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    corollary22DegreeDiffNatDegreeLeThreeNonconstantStatement :=
  corollary22DegreeDiffNatDegreeLeThreeNonconstant_of_theorem21NatDegreeLeThree
    (theorem21CompatibleRootCountNatDegreeLeThreeNonconstant_of_forward
      hforward)

/-- Liu Corollary 2.2 follows from the isolated branch-retaining
common-interleaver forward direction. -/
theorem corollary22DegreeDiff_of_commonForward
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement) :
    corollary22DegreeDiffStatement :=
  fun _ _ hf hg hsgn hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
        (hforward hf hg hsgn hcompat))

/-- The nonconstant Liu Corollary 2.2 follows from the isolated nonconstant
branch-retaining common-interleaver forward direction. -/
theorem corollary22DegreeDiffNonconstant_of_commonForward
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement) :
    corollary22DegreeDiffNonconstantStatement :=
  fun _ _ hf hg hsgn hf_deg hg_deg hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
        (hforward hf hg hsgn hf_deg hg_deg hcompat))

/-- Liu Corollary 2.2 follows from the isolated forward direction of
Theorem 2.1. -/
theorem corollary22DegreeDiff_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    corollary22DegreeDiffStatement :=
  corollary22DegreeDiff_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)

/-- The nonconstant Liu Corollary 2.2 follows from the isolated nonconstant
forward direction of Theorem 2.1. -/
theorem corollary22DegreeDiffNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    corollary22DegreeDiffNonconstantStatement :=
  corollary22DegreeDiffNonconstant_of_commonForward
    (theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstant_of_forward
      hforward)

/-- Liu Corollary 2.2 follows from the Theorem 2.1 compatibility criterion. -/
theorem corollary22DegreeDiff_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    corollary22DegreeDiffStatement :=
  corollary22DegreeDiff_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)

/-- Nonconstant Liu Corollary 2.2 follows from the nonconstant Theorem 2.1
compatibility criterion. -/
theorem corollary22DegreeDiffNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    corollary22DegreeDiffNonconstantStatement :=
  corollary22DegreeDiffNonconstant_of_forward
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)

theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff (corollary22DegreeDiff_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

theorem
    natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff_nonconstant
    (corollary22DegreeDiffNonconstant_of_theorem21CompatibleRootCount h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Direct degree-gap consequence via the swapped branch projection of
Liu Theorem 2.1. -/
theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm hf hg hsgn
    (theorem21RootCountBranches_symm_of_compatible h hf hg hsgn hcompat)

/-- Nonconstant direct degree-gap consequence via the swapped branch
projection of Liu Theorem 2.1. -/
theorem
    natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm hf hg hsgn
    (theorem21RootCountBranches_symm_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg hcompat)

end LiuOppositeSigns
end RealRooted
