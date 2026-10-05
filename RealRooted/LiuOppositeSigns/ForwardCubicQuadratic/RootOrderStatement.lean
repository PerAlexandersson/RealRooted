import RealRooted.LiuOppositeSigns.ForwardLowDegree
import RealRooted.SameDegreeCubicRootCount

/-!
# Liu cubic/quadratic root-data branches

This module contains the explicit root-data branch constructors used in the
degree-three/two forward direction of Liu Theorem 2.1.
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

end LiuOppositeSigns
end RealRooted
