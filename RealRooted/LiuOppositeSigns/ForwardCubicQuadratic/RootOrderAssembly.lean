import RealRooted.LiuOppositeSigns.CommonInterleaverConsequences
import RealRooted.LiuOppositeSigns.ForwardCubicLinear
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderLower
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderMiddle
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderStatement
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderUpper

/-!
# Liu cubic/quadratic root-order assembly

This module contains the conditional degree-three/two root-order assembly
packages used by the nonconstant no-common forward direction of Liu
Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Root-order obstruction for compatible opposite-sign cubic/quadratic pairs. -/
theorem compatibleCubicPairRootOrder : CompatibleCubicPairRootOrderStatement := by
  intro f g a b c u v hf hg hsgn hcompat _hfdeg _hgdeg hab hbc huv
    hfroots hgroots
  have hvc :
      v ≤ c :=
    upper_quadratic_root_le_upper_cubic_root_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hfroots hgroots
  have hub :
      u ≤ b :=
    lower_quadratic_root_le_middle_cubic_root_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hvc hfroots hgroots
  have hav :
      a ≤ v :=
    lower_cubic_root_le_upper_quadratic_root_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hfroots hgroots
  exact ⟨hub, hav, hvc⟩

/-- Degree `(3, 2)` forward endpoint case. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_three_two
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 2) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_three_two_of_cubicPairRootOrder
    compatibleCubicPairRootOrder hf hg hsgn hcompat hfdeg hgdeg

/-- Degree `(2, 3)` no-common forward endpoint case.  The no-common-root
hypothesis makes the largest-root comparison strict after swapping the pair. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_two_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 3) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_two_three_of_cubicPairRootOrder
    compatibleCubicPairRootOrder hf hg hsgn hcompat hno hfdeg hgdeg

/-- Mixed degree-three/two no-common forward endpoint package. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_three_two_or_two_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hdeg :
      (f.natDegree = 3 ∧ g.natDegree = 2) ∨
        (f.natDegree = 2 ∧ g.natDegree = 3)) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_natDegree_three_two_or_two_three_of_cubicPairRootOrder
    compatibleCubicPairRootOrder hf hg hsgn hcompat hno hdeg

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

/-- Conditional nonconstant no-common forward direction through endpoint
degree three, excluding the cubic/cubic corner and using the checked
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

/-- Nonconstant no-common forward direction through endpoint degree three,
excluding the cubic/cubic corner. -/
theorem theorem21RootCountBranches_of_natDegree_le_three_excluding_three_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g)
    (hno : NoCommonRoots f g)
    (hfdeg_ne : f.natDegree ≠ 0) (hgdeg_ne : g.natDegree ≠ 0)
    (hfdeg_le : f.natDegree ≤ 3) (hgdeg_le : g.natDegree ≤ 3)
    (hnot_three_three : ¬ (f.natDegree = 3 ∧ g.natDegree = 3)) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_natDegree_le_three_excluding_three_three_of_cubicPairRootOrder
    compatibleCubicPairRootOrder hf hg hsgn hcompat hno
    hfdeg_ne hgdeg_ne hfdeg_le hgdeg_le hnot_three_three

end LiuOppositeSigns
end RealRooted
