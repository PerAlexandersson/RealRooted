module

import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RightSuccessor
import RealRooted.LiuOppositeSigns.XSub.SameDegree
import RealRooted.LiuOppositeSigns.PositiveSplitPair
public import RealRooted.LiuOppositeSigns.PositiveSplitRootCount
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.QuadraticRoot

/-!
# Liu linear/quadratic x-subtraction leaf

This module contains the normalized linear/quadratic positive-split
x-subtraction leaf used by the right-successor right-degree-two endpoint.
-/

public section

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

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
      ite_eq_right (not_le.mpr hcx)]
    simp
  have hg_count : rootCountAtOrAbove g x = 2 := by
    rw [rootCountAtOrAbove, hgroots]
    simp only [Multiset.insert_eq_cons]
    rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), ite_eq_left hxb]
    simp
  rw [hf_count, hg_count] at hcount
  norm_num at hcount

/-- Explicit discriminant certificate for the normalized case
`a ≤ c ≤ b ≤ 0`. -/
lemma xSubLinearQuadraticDiscrimNonneg_between
    {u v w μ : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
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

/-- The discriminant of the normalized degree-one/degree-two x-subtraction
pencil is nonnegative. -/
theorem xSubLinearQuadraticDiscrimNonneg {a b c μ : ℝ} (hab : a ≤ b) (hac : a ≤ c) (hb0 : b ≤ 0)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    0 ≤ discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) := by
  by_cases hcb : c ≤ b
  · let u : ℝ := c - a
    let v : ℝ := b - c
    let w : ℝ := -b
    have hu : 0 ≤ u := by
      dsimp [u]
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
    exact xSubLinearQuadraticDiscrimNonneg_between hu hw hμ
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

/-- The normalized monic degree-one/degree-two x-subtraction pencil splits. -/
theorem xSubLinearQuadraticSplits {a b c μ : ℝ} (hab : a ≤ b) (hac : a ≤ c)
    (hb0 : b ≤ 0) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * (X - C c) - C μ * ((X - C a) * (X - C b))).Splits := by
  have hpoly :
      X * (X - C c) - C μ * ((X - C a) * (X - C b)) =
        C (1 - μ) * X ^ 2 + C (-c + μ * (a + b)) * X +
          C (-μ * (a * b)) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1]
    ring_nf
  have hdisc : 0 ≤ discrim (1 - μ) (-c + μ * (a + b)) (-μ * (a * b)) :=
    xSubLinearQuadraticDiscrimNonneg hab hac hb0 hc0 hμ
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg_or_linear hdisc

/-- Degree-one/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_one_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  exact hpair.xSub_splits_of_right_successor_nonneg hpnn hqnn (by lia) hμ

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
  have hfdeg : f.natDegree = 1 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 2 := by simpa [Polynomial.natDegree_comp] using hgdeg
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
      hdeg hone
  · have htwo : g.natDegree = 2 := by lia
    exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
      hpair hfnn hgnn hdeg htwo

end LiuOppositeSigns
end RealRooted
