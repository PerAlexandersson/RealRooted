import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RightProtruding
import RealRooted.LiuOppositeSigns.ForwardLowDegree
import RealRooted.SameDegreeCubicRootCount

/-!
# Liu cubic/quadratic upper root-order exclusions

This module contains the upper-side root-order exclusions for the degree
`(3, 2)` forward direction of Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

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
rules out the tangent-at-`v` right-protruding side-condition branch. -/
lemma not_right_protruding_tangent_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u < v)
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c))
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
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
    not_compatible_scaled_cubic_quadratic_of_opposite_of_right_protruding_tangent
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc huv hcv hside hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out the negative-side right-protruding branch. -/
lemma not_right_protruding_side_neg_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) < 0)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
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
    not_compatible_scaled_cubic_quadratic_of_opposite_of_right_protruding_side_neg
      (A := f.leadingCoeff) (B := g.leadingCoeff)
      hsgn hab hbc hcv hside hcompat_fac

/-- In an arbitrary split opposite-sign cubic/quadratic pair, compatibility
rules out every right-protruding branch. -/
lemma not_right_protruding_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    ¬ c < v := by
  intro hcv
  by_cases huv_lt : u < v
  · by_cases hside_nonneg :
      0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
        (a * b + a * c + b * c)
    · exact
        not_right_protruding_tangent_of_compatible_natDegree_three_two
          hf hg hsgn hcompat hab hbc huv_lt hside_nonneg hfroots hgroots hcv
    · exact
        not_right_protruding_side_neg_of_compatible_natDegree_three_two
          hf hg hsgn hcompat hab hbc (lt_of_not_ge hside_nonneg)
          hfroots hgroots hcv
  · have huv_eq : u = v := le_antisymm huv (le_of_not_gt huv_lt)
    subst v
    exact
      not_right_roots_above_of_compatible_natDegree_three_two
        hf hg hsgn hcompat hab hbc le_rfl hfroots hgroots hcv

/-- Upper root bound for a compatible opposite-sign cubic/quadratic pair. -/
lemma upper_quadratic_root_le_upper_cubic_root_of_compatible_natDegree_three_two
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    v ≤ c := by
  by_contra hnot
  exact
    not_right_protruding_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hfroots hgroots
      (lt_of_not_ge hnot)

end LiuOppositeSigns
end RealRooted
