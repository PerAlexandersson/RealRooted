import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.MiddleGap
import RealRooted.SameDegreeCubicRootCount

/-!
# Liu cubic/quadratic middle root-order exclusions

This module lifts the middle-gap cubic/quadratic obstruction to arbitrary
split opposite-sign cubic/quadratic pairs.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- In an arbitrary split opposite-sign cubic/quadratic pair with distinct
quadratic roots and upper quadratic root at most the upper cubic root,
compatibility rules out the case where both quadratic roots lie strictly to the
right of the middle cubic root. -/
lemma not_middle_gap_distinct_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hbu : b < u) (huv : u < v) (hvc : v ≤ c)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    False := by
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
    not_compatible_scaled_cubic_quadratic_of_opposite_of_middle_gap_distinct
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc hbu huv hvc hcompat_fac

/-- Distinct-root middle-bound form for a compatible opposite-sign
cubic/quadratic pair. -/
lemma lower_quadratic_root_le_middle_cubic_root_of_compatible_natDegree_three_two_of_distinct
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u < v) (hvc : v ≤ c)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    u ≤ b := by
  by_contra hnot
  exact
    (not_middle_gap_distinct_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc (lt_of_not_ge hnot) huv hvc
      hfroots hgroots).elim

/-- In an arbitrary split opposite-sign cubic/quadratic pair whose upper
quadratic root is at most the upper cubic root, compatibility rules out the
case where both quadratic roots lie strictly to the right of the middle cubic
root. -/
lemma not_middle_gap_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hbu : b < u) (huv : u ≤ v) (hvc : v ≤ c)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    False := by
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
    not_compatible_scaled_cubic_quadratic_of_opposite_of_middle_gap
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc hbu huv hvc hcompat_fac

/-- Middle-bound form for a compatible opposite-sign cubic/quadratic pair
once the upper quadratic root is known to be at most the upper cubic root. -/
lemma lower_quadratic_root_le_middle_cubic_root_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hvc : v ≤ c)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    u ≤ b := by
  by_contra hnot
  exact
    (not_middle_gap_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc (lt_of_not_ge hnot) huv hvc
      hfroots hgroots).elim

end LiuOppositeSigns
end RealRooted
