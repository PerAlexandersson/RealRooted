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

/-- Tangency side-condition form of the upper root bound for a compatible
opposite-sign cubic/quadratic pair. -/
lemma upper_quadratic_root_le_upper_cubic_root_of_tangent_side
    {f g : ℝ[X]} {a b c u v : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u < v)
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c))
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v}) :
    v ≤ c := by
  by_contra hnot
  exact
    not_right_protruding_tangent_of_compatible_natDegree_three_two
      hf hg hsgn hcompat hab hbc huv hside hfroots hgroots
      (lt_of_not_ge hnot)

end LiuOppositeSigns
end RealRooted
