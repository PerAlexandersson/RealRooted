module

import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.LeftSuccessor
import RealRooted.CommonInterleaver.RootCountCombinatorics
public import RealRooted.CubicDiscriminant
import RealRooted.LiuOppositeSigns.PositiveSplitPair
public import RealRooted.QuadraticRoot
import RealRooted.SameDegreeQuadraticRootCount
public import RealRooted.LiuOppositeSigns.PositiveSplitRootCount
import RealRooted.Linear

/-!
# Liu left-successor x-subtraction base cases

This module specializes the general left-successor splitting theorem to the
quadratic/linear pencil. Splitting also gives its cubic discriminant certificates.
-/

public section

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Quadratic terminal case for the x-subtraction pencil: a degree-one
positive-leading left endpoint and degree-zero positive-leading right endpoint
give a splitting polynomial `X * p - μ q` for every `μ > 0`. -/
lemma splits_X_mul_sub_C_mul_of_natDegree_one_zero
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p)
    (hq_pos : HasPosLeadingCoeff q) (hpdeg : p.natDegree = 1)
    (hqdeg : q.natDegree = 0) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let a := p.coeff 1
  let b := p.coeff 0
  let c := q.coeff 0
  have hp_eq : p = C a * X + C b := by
    simpa [a, b] using Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le
  have hq_eq : q = C c := by simpa [c] using Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have ha_pos : 0 < a := by simpa [HasPosLeadingCoeff, hpdeg, leadingCoeff, a] using hp_pos
  have hc_pos : 0 < c := by simpa [HasPosLeadingCoeff, hqdeg, leadingCoeff, c] using hq_pos
  have hpoly : X * p - C μ * q = C a * X ^ 2 + C b * X + C (-μ * c) := by
    rw [hp_eq, hq_eq]
    simp [C_mul, C_neg]
    ring
  have hprod : 0 < 4 * a * μ * c := by positivity
  have hdisc : 0 ≤ discrim a b (-μ * c) := by
    rw [discrim]
    linarith [sq_nonneg b, hprod]
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg ha_pos.ne' hdisc

/-- Degree-zero right endpoint base case for the sign-normalized x-subtraction
leaf. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 1 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 0 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_natDegree_one_zero
    (hpair.left_pos.comp_X_add_C r) (hpair.right_pos.comp_X_add_C r)
    hFdeg hGdeg hμ

/-- A normalized quadratic/linear pair is covered by the general left-successor theorem. -/
private lemma normalized_left_successor {a b c μ : ℝ} (hab : a ≤ b) (hac : a ≤ c)
    (hb0 : b ≤ 0) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) - C μ * (X - C c)).Splits := by
  let p : ℝ[X] := (X - C a) * (X - C b)
  let q : ℝ[X] := X - C c
  let k : ℝ[X] := (X - C (min b c)) * (X - C (max b c))
  have hp : p.Monic := (monic_X_sub_C a).mul (monic_X_sub_C b)
  have hq : q.Monic := monic_X_sub_C c
  have hk : k.Monic := (monic_X_sub_C (min b c)).mul (monic_X_sub_C (max b c))
  have hp_split : p.Splits := (Splits.X_sub_C a).mul (Splits.X_sub_C b)
  have hq_split : q.Splits := Splits.X_sub_C c
  have hk_split : k.Splits :=
    (Splits.X_sub_C (min b c)).mul (Splits.X_sub_C (max b c))
  have hp_roots : p.roots = (↑[a, b] : Multiset ℝ) := by
    change p.roots = {a, b}
    simp [p, roots_mul, X_sub_C_ne_zero]
  have hq_roots : q.roots = (↑[c] : Multiset ℝ) := roots_X_sub_C c
  have hk_roots : k.roots = (↑[min b c, max b c] : Multiset ℝ) := by
    change k.roots = {min b c, max b c}
    simp [k, roots_mul, X_sub_C_ne_zero]
  have hpk : StrictInterl p k := by
    refine ⟨⟨hp.ne_zero, hp_split⟩, ⟨hk.ne_zero, hk_split⟩,
      [a, b], [min b c, max b c], ?_, ?_, hp_roots.symm, hk_roots.symm, Or.inr ?_⟩
    · simp [hab]
    · grind [List.pairwise_cons, le_max_iff, min_le_iff]
    · exact ⟨rfl, by simp [ListAlternates, ListInterlaces, hab, hac, le_min_iff]⟩
  have hqk : StrictInterl q k := by
    refine ⟨⟨hq.ne_zero, hq_split⟩, ⟨hk.ne_zero, hk_split⟩,
      [c], [min b c, max b c], ?_, ?_, hq_roots.symm, hk_roots.symm, Or.inl ?_⟩
    · simp
    · grind [List.pairwise_cons, le_max_iff, min_le_iff]
    · exact ⟨rfl, by simp [ListInterlaces]⟩
  have hpair : PositiveSplitRootCountPair p q := by
    refine ⟨hasPosLeadingCoeff_of_monic hp, hasPosLeadingCoeff_of_monic hq,
      hp_split, hq_split, ?_⟩
    apply RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot hp.ne_zero hq.ne_zero
    intro x _ _
    have hpdeg : k.natDegree = p.natDegree := by
      simp [p, k, natDegree_mul, X_sub_C_ne_zero]
    have hpbound :=
      (sameDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
        hk_split hp_split hpdeg.symm x).mpr
          (sameDegreeRootCountOriented_of_strictInterl hpk hpdeg x)
    have hqbound := succDegreeRootCountAboveOriented_of_strictInterl hqk
      (by simp [q, k, natDegree_mul, X_sub_C_ne_zero]) x
    constructor <;> lia
  exact hpair.xSub_splits_of_left_successor_nonneg
    ((hasNonnegCoeffs_X_sub_C (hab.trans hb0)).mul (hasNonnegCoeffs_X_sub_C hb0))
    (hasNonnegCoeffs_X_sub_C hc0)
    (by simp [p, q, natDegree_mul, X_sub_C_ne_zero]) hμ

/-- Splitting, rather than an expanded sum of squares, certifies the cubic discriminant. -/
private lemma normalized_left_discr_nonneg {a b c μ : ℝ} (hab : a ≤ b) (hac : a ≤ c)
    (hb0 : b ≤ 0) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    0 ≤ cubicDiscr (X * ((X - C a) * (X - C b)) - C μ * (X - C c)) := by
  exact cubicDiscr_nonneg_of_splits_natDegree_le_three (by compute_degree)
    (normalized_left_successor hab hac hb0 hc0 hμ)

/-- Explicit discriminant certificate for the normalized case
`a ≤ c ≤ b ≤ 0`. -/
lemma xSubQuadraticLinearCubicDiscrimNonneg_between
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hμ : 0 < μ) :
    0 ≤ cubicDiscr
      (X * ((X - C (-(u + v + w))) * (X - C (-w))) -
        C μ * (X - C (-(v + w)))) := by
  apply normalized_left_discr_nonneg <;> linarith

/-- Explicit discriminant certificate for the normalized case
`a ≤ b ≤ c ≤ 0`. -/
lemma xSubQuadraticLinearCubicDiscrimNonneg_right
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hμ : 0 < μ) :
    0 ≤ cubicDiscr
      (X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
        C μ * (X - C (-w))) := by
  apply normalized_left_discr_nonneg <;> linarith

/-- The cubic discriminant of the normalized degree-two/degree-one
x-subtraction pencil is nonnegative. -/
theorem xSubQuadraticLinearCubicDiscrimNonneg {a b c μ : ℝ} (hab : a ≤ b) (hac : a ≤ c)
    (hb0 : b ≤ 0) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    0 ≤ cubicDiscr (X * ((X - C a) * (X - C b)) - C μ * (X - C c)) := by
  exact normalized_left_discr_nonneg hab hac hb0 hc0 hμ

/-- Degree-two/degree-one positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_one
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 1)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  exact hpair.xSub_splits_of_left_successor_nonneg hpnn hqnn (by lia) hμ

/-- Degree-one right endpoint case for the sign-normalized x-subtraction
leaf. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg_shift : (f.comp (X + C r)).natDegree = 2 := by
    have hfdeg : f.natDegree = 2 := by lia
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hgdeg_shift : (g.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_one
    (hpair.comp_X_add_C r) hfnn hgnn hfdeg_shift hgdeg_shift hμ

end LiuOppositeSigns
end RealRooted
