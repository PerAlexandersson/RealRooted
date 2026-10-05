import RealRooted.CubicDiscriminant
import RealRooted.LiuOppositeSigns.PositiveSplitPair
import RealRooted.QuadraticRoot
import RealRooted.SameDegreeQuadraticRootCount

/-!
# Liu left-successor x-subtraction base cases

This module contains low-degree right-endpoint cases of the left-successor
positive-split x-subtraction pencil used by the two-degree factor-return
branch.
-/

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
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (_hgnn : HasNonnegCoeffs (g.comp (X + C r)))
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

/-- Explicit discriminant certificate for the normalized case
`a ≤ c ≤ b ≤ 0`. -/
lemma xSubQuadraticLinearCubicDiscrimNonneg_between
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hμ : 0 < μ) :
    0 ≤ cubicDiscr
      (X * ((X - C (-(u + v + w))) * (X - C (-w))) -
        C μ * (X - C (-(v + w)))) := by
  have hpoly :
      X * ((X - C (-(u + v + w))) * (X - C (-w))) -
          C μ * (X - C (-(v + w))) =
        C 1 * X ^ 3 + C (u + v + 2 * w) * X ^ 2 +
          C ((u + v + w) * w - μ) * X + C (-μ * (v + w)) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1, C_ofNat]
    ring_nf
  have hdisc :
      cubicDiscr
          (X * ((X - C (-(u + v + w))) * (X - C (-w))) -
            C μ * (X - C (-(v + w)))) =
        (μ - v ^ 2 - v * w) ^ 2 * (4 * μ + w ^ 2) +
          u *
            (μ ^ 2 * u + 20 * μ ^ 2 * v + 4 * μ * u ^ 2 * v +
              12 * μ * u * v ^ 2 + 12 * μ * v ^ 3 + 10 * μ ^ 2 * w +
              2 * μ * u ^ 2 * w + 12 * μ * u * v * w +
              18 * μ * v ^ 2 * w + 8 * μ * u * w ^ 2 + u ^ 3 * w ^ 2 +
              10 * μ * v * w ^ 2 + 4 * u ^ 2 * v * w ^ 2 +
              6 * u * v ^ 2 * w ^ 2 + 4 * v ^ 3 * w ^ 2 +
              2 * μ * w ^ 3 + 2 * u ^ 2 * w ^ 3 + 6 * u * v * w ^ 3 +
              6 * v ^ 2 * w ^ 3 + u * w ^ 4 + 2 * v * w ^ 4) := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- Explicit discriminant certificate for the normalized case
`a ≤ b ≤ c ≤ 0`. -/
lemma xSubQuadraticLinearCubicDiscrimNonneg_right
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hμ : 0 < μ) :
    0 ≤ cubicDiscr
      (X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
        C μ * (X - C (-w))) := by
  have hpoly :
      X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
          C μ * (X - C (-w)) =
        C 1 * X ^ 3 + C (u + 2 * v + 2 * w) * X ^ 2 +
          C ((u + v + w) * (v + w) - μ) * X + C (-μ * w) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1, C_ofNat]
    ring_nf
  have hdisc :
      cubicDiscr
          (X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
            C μ * (X - C (-w))) =
        (4 * μ + u ^ 2) * (μ - u * v - v ^ 2) ^ 2 +
          w *
            (10 * μ ^ 2 * u + 2 * μ * u ^ 3 + 20 * μ ^ 2 * v +
              10 * μ * u ^ 2 * v + 2 * u ^ 4 * v +
              18 * μ * u * v ^ 2 + 6 * u ^ 3 * v ^ 2 +
              12 * μ * v ^ 3 + 4 * u ^ 2 * v ^ 3 + μ ^ 2 * w +
              8 * μ * u ^ 2 * w + u ^ 4 * w + 12 * μ * u * v * w +
              6 * u ^ 3 * v * w + 12 * μ * v ^ 2 * w +
              6 * u ^ 2 * v ^ 2 * w + 2 * μ * u * w ^ 2 +
              2 * u ^ 3 * w ^ 2 + 4 * μ * v * w ^ 2 +
              4 * u ^ 2 * v * w ^ 2 + u ^ 2 * w ^ 3) := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- The cubic discriminant of the normalized degree-two/degree-one
x-subtraction pencil is nonnegative. -/
theorem xSubQuadraticLinearCubicDiscrimNonneg {a b c μ : ℝ} (hab : a ≤ b) (hac : a ≤ c)
    (hb0 : b ≤ 0) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    0 ≤ cubicDiscr (X * ((X - C a) * (X - C b)) - C μ * (X - C c)) := by
  by_cases hcb : c ≤ b
  · let u : ℝ := c - a
    let v : ℝ := b - c
    let w : ℝ := -b
    have hu : 0 ≤ u := by
      dsimp [u]
      linarith
    have hv : 0 ≤ v := by
      dsimp [v]
      linarith
    have hw : 0 ≤ w := by
      dsimp [w]
      linarith
    have hnorm :
        X * ((X - C a) * (X - C b)) - C μ * (X - C c) =
          X * ((X - C (-(u + v + w))) * (X - C (-w))) -
            C μ * (X - C (-(v + w))) := by
      dsimp [u, v, w]
      ring_nf
    rw [hnorm]
    exact xSubQuadraticLinearCubicDiscrimNonneg_between hu hv hw hμ
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
    have hnorm :
        X * ((X - C a) * (X - C b)) - C μ * (X - C c) =
          X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
            C μ * (X - C (-w)) := by
      dsimp [u, v, w]
      ring_nf
    rw [hnorm]
    exact xSubQuadraticLinearCubicDiscrimNonneg_right hu hv hw hμ

/-- Degree-two/degree-one positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_one
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 1)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, hab, hproots, hpfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.left_splits hpdeg
  obtain ⟨c, hqroots, hqfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hpair.right_splits hqdeg
  have hac : a ≤ c :=
    left_root_le_singleton_root_of_positiveSplitRootCountPair_two_one
      hpair hab hproots hqroots
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn b hb_mem
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ q.roots := by
      rw [hqroots]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn c hc_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] := X * ((X - C a) * (X - C b)) - C ν * (X - C c)
  have hinner_deg : inner.natDegree ≤ 3 := by
    dsimp [inner]
    compute_degree
  have hinner_disc : 0 ≤ cubicDiscr inner := by
    dsimp [inner]
    exact xSubQuadraticLinearCubicDiscrimNonneg hab hac hb0 hc0 hν_pos
  have hinner_splits : inner.Splits :=
    splits_of_natDegree_le_three_cubicDiscr_nonneg hinner_deg hinner_disc
  have hpfacA : p = C A * ((X - C a) * (X - C b)) := by simpa [A] using hpfac
  have hqfacB : q = C B * (X - C c) := by simpa [B] using hqfac
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfacA, hqfacB]
    dsimp [inner, ν]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hA_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

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
