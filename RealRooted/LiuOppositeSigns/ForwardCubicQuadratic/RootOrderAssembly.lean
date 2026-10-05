import RealRooted.LiuOppositeSigns.CommonInterleaverConsequences
import RealRooted.LiuOppositeSigns.ForwardCubicLinear
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderLower
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderMiddle
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderStatement
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderUpper

/-!
# Liu cubic/quadratic root-order assembly

This module proves the cubic/quadratic root-order obstruction and the
resulting degree `(3, 2)`, `(2, 3)`, and endpoint-degree-three cases of the
nonconstant no-common forward direction of Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Root-order obstruction for compatible opposite-sign cubic/quadratic pairs. -/
theorem compatibleCubicPairRootOrder {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g)
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    u ≤ b ∧ a ≤ v ∧ v ≤ c := by
  have hvc :
      v ≤ c :=
    upper_quadratic_root_le_upper_cubic_root_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hfroots hgroots
  have hub :
      u ≤ b :=
    lower_quadratic_root_le_middle_cubic_root_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab huv hvc hfroots hgroots
  have hav :
      a ≤ v :=
    lower_cubic_root_le_upper_quadratic_root_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hfroots hgroots
  exact ⟨hub, hav, hvc⟩

/-- Degree `(3, 2)` no-common forward endpoint case.  The cubic/quadratic
root-order obstruction and the explicit deletion-branch constructor give Liu's
root-count branch. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_three_two
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
    compatibleCubicPairRootOrder hf hg hsgn hcompat hab hbc huv hfroots hgroots
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

/-- Degree `(2, 3)` no-common forward endpoint case, obtained by
applying the cubic/quadratic root-order obstruction after swapping the pair. -/
theorem
    theorem21RootCountBranches_of_compatible_natDegree_two_three
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
    compatibleCubicPairRootOrder (f := g) (g := f) (a := c) (b := d) (c := e)
      (u := a) (v := b)
      hg hf hsgn.symm hcompat.comm hcd hde hab hgroots
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

/-- Nonconstant no-common forward direction through endpoint degree three,
excluding the cubic/cubic corner. -/
theorem
    theorem21RootCountBranches_of_natDegree_le_three_excluding_three_three
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
          theorem21RootCountBranches_of_compatible_natDegree_one_three
            hf hg hsgn hcompat hno hf_one hg_three
      · exact
          theorem21RootCountBranches_of_compatible_natDegree_two_three
            hf hg hsgn hcompat hno hf_two hg_three
  · have hf_three : f.natDegree = 3 := by lia
    by_cases hg_le_two : g.natDegree ≤ 2
    · have hg_cases : g.natDegree = 1 ∨ g.natDegree = 2 := by
        have hg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hgdeg_ne
        interval_cases g.natDegree <;> simp_all
      rcases hg_cases with hg_one | hg_two
      · exact
          theorem21RootCountBranches_of_compatible_natDegree_three_one
            hf hg hsgn hcompat hf_three hg_one
      · exact
          theorem21RootCountBranches_of_compatible_natDegree_three_two
            hf hg hsgn hcompat hf_three hg_two
    · have hg_three : g.natDegree = 3 := by lia
      exact False.elim (hnot_three_three ⟨hf_three, hg_three⟩)

end LiuOppositeSigns
end RealRooted
