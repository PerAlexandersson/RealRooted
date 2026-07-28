import RealRooted.LiuOppositeSigns.FactorReturnAssembly
import RealRooted.LiuOppositeSigns.XSub.LeftSucc
import RealRooted.LiuOppositeSigns.XSub.SameDegree
import RealRooted.LiuOppositeSigns.XSub.LinearQuadratic
import RealRooted.LiuOppositeSigns.XSub.QuadraticCubic
import RealRooted.LiuOppositeSigns.XSub.QuadraticQuadratic
import RealRooted.LiuOppositeSigns.XSub.CubicCubic
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
