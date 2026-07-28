import RealRooted.LiuOppositeSigns.CommonInterleaverConsequences
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.Average
import RealRooted.LiuOppositeSigns.ForwardCubicLinear

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
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

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

end LiuOppositeSigns
end RealRooted
