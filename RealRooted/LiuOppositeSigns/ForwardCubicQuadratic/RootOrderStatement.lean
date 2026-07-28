import RealRooted.LiuOppositeSigns.ForwardLowDegree
import RealRooted.SameDegreeCubicRootCount

/-!
# Liu cubic/quadratic root-order statement wrappers

This module contains the conditional cubic/quadratic root-order interface and
the branch wrappers that consume it in the degree-three/two forward direction
of Liu Theorem 2.1.
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

end LiuOppositeSigns
end RealRooted
