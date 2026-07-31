import RealRooted.LiuOppositeSigns.XSub.CubicCubic

/-!
# Liu cubic/quadratic average-above obstruction

This module contains the shared cubic-minus-quadratic coefficient tools and
the average-above/right-roots-above obstruction branch used in the
degree-three/two forward direction of Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Coefficient expansion of a monic cubic minus a monic quadratic. -/
lemma cubicSubQuadratic_eq_cubic_expansion (a b c u v μ : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v)) =
      C 1 * X ^ 3 + C (-(a + b + c + μ)) * X ^ 2 +
        C (a * b + a * c + b * c + μ * (u + v)) * X +
          C (-(a * b * c) - μ * (u * v)) := by
  simp only [C_add, C_mul, C_neg, C_sub, C_1]
  ring

/-- The cubic discriminant is invariant under translating a cubic written in
coefficient form. -/
lemma cubicDiscr_cubic_comp_X_add_C (a3 a2 a1 a0 r : ℝ) :
    cubicDiscr
        ((C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).comp
          (X + C r)) =
      cubicDiscr (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0) := by
  have hpoly :
      (C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0).comp
          (X + C r) =
        C a3 * X ^ 3 + C (3 * a3 * r + a2) * X ^ 2 +
          C (3 * a3 * r ^ 2 + 2 * a2 * r + a1) * X +
            C (a3 * r ^ 3 + a2 * r ^ 2 + a1 * r + a0) := by
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [hpoly, cubicDiscr_of_coeffs, cubicDiscr_of_coeffs]
  ring

/-- Translating the variable preserves the cubic discriminant of a monic
cubic-minus-quadratic pencil. -/
lemma cubicDiscr_cubicSubQuadratic_comp_X_add_C
    (a b c u v μ r : ℝ) :
    cubicDiscr
        ((((X - C a) * (X - C b) * (X - C c)) -
            C μ * ((X - C u) * (X - C v))).comp (X + C r)) =
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) := by
  rw [cubicSubQuadratic_eq_cubic_expansion]
  exact
    cubicDiscr_cubic_comp_X_add_C
      1 (-(a + b + c + μ))
      (a * b + a * c + b * c + μ * (u + v))
      (-(a * b * c) - μ * (u * v)) r

/-- The midpoint tangent coefficient is positive when the average of the
quadratic roots lies strictly above the cubic root interval. -/
lemma cubicSubQuadratic_average_above_mu_pos {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcmean : c < (u + v) / 2) :
    0 < 3 * ((u + v) / 2) - (a + b + c) := by
  let m : ℝ := (u + v) / 2
  have hcm : c < m := by
    simpa [m] using hcmean
  have hma : 0 < m - a := by linarith
  have hmb : 0 < m - b := by linarith
  have hmc : 0 < m - c := by linarith
  have hsum :
      3 * m - (a + b + c) = (m - a) + (m - b) + (m - c) := by
    ring
  change 0 < 3 * m - (a + b + c)
  rw [hsum]
  nlinarith

/-- With the midpoint tangent coefficient, the derivative discriminant of the
cubic-minus-quadratic pencil is negative when the average of the quadratic
roots lies strictly above the cubic root interval. -/
lemma cubicSubQuadratic_average_above_deriv_disc_neg {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcmean : c < (u + v) / 2) :
    (a + b + c + (3 * ((u + v) / 2) - (a + b + c))) ^ 2 <
      3 *
        (a * b + a * c + b * c +
          (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) := by
  let m : ℝ := (u + v) / 2
  have hcm : c < m := by
    simpa [m] using hcmean
  have hma : 0 < m - a := by linarith
  have hmb : 0 < m - b := by linarith
  have hmc : 0 < m - c := by linarith
  have hp1 : 0 < (m - a) * (m - b) := mul_pos hma hmb
  have hp2 : 0 < (m - a) * (m - c) := mul_pos hma hmc
  have hp3 : 0 < (m - b) * (m - c) := mul_pos hmb hmc
  have hsum_pos :
      0 < (m - a) * (m - b) + (m - a) * (m - c) +
        (m - b) * (m - c) := by
    nlinarith
  have hdelta :
      3 *
          (a * b + a * c + b * c +
            (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) -
          (a + b + c + (3 * ((u + v) / 2) - (a + b + c))) ^ 2 =
        3 * ((m - a) * (m - b) + (m - a) * (m - c) +
          (m - b) * (m - c)) := by
    dsimp [m]
    ring
  nlinarith

/-- Derivative-discriminant certificate for a negative cubic discriminant of a
monic cubic-minus-quadratic pencil. -/
lemma cubicDiscr_cubicSubQuadratic_neg_of_deriv_disc_neg
    {a b c u v μ : ℝ}
    (hderiv :
      (a + b + c + μ) ^ 2 <
        3 * (a * b + a * c + b * c + μ * (u + v))) :
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) < 0 := by
  rw [cubicSubQuadratic_eq_cubic_expansion]
  have hderiv' :
      (-(a + b + c + μ)) ^ 2 <
        3 * 1 * (a * b + a * c + b * c + μ * (u + v)) := by
    nlinarith
  exact
    cubicDiscr_neg_of_deriv_disc_neg
      1
      (-(a + b + c + μ))
      (a * b + a * c + b * c + μ * (u + v))
      (-(a * b * c) - μ * (u * v))
      (by norm_num) hderiv'

/-- Critical-value certificate for a negative cubic discriminant of a monic
cubic-minus-quadratic pencil. -/
lemma cubicDiscr_cubicSubQuadratic_neg_of_critical_value
    {a b c u v μ t y : ℝ}
    (hcrit :
      3 * t ^ 2 - 2 * (a + b + c + μ) * t +
        (a * b + a * c + b * c + μ * (u + v)) = 0)
    (hvalue :
      y =
        (t - a) * (t - b) * (t - c) -
          μ * ((t - u) * (t - v)))
    (hy : y ≠ 0)
    (hsign :
      0 ≤ y * (3 * t - (a + b + c + μ)) ^ 3) :
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) < 0 := by
  have hcrit' :
      3 * t ^ 2 + 2 * (-(a + b + c + μ)) * t +
        (a * b + a * c + b * c + μ * (u + v)) = 0 := by
    nlinarith
  have hvalue' :
      y =
      t ^ 3 + (-(a + b + c + μ)) * t ^ 2 +
          (a * b + a * c + b * c + μ * (u + v)) * t +
            (-(a * b * c) - μ * (u * v)) := by
    rw [hvalue]
    ring
  have hsign' :
      0 ≤ y * (3 * t + (-(a + b + c + μ))) ^ 3 := by
    simpa [sub_eq_add_neg] using hsign
  rw [cubicSubQuadratic_eq_cubic_expansion]
  exact
    cubicDiscr_neg_of_critical_value
      (p := -(a + b + c + μ))
      (q := a * b + a * c + b * c + μ * (u + v))
      (r := -(a * b * c) - μ * (u * v))
      (t := t) (y := y) hcrit' hvalue' hy hsign'

/-- A negative cubic discriminant certifies that the cubic-minus-quadratic
pencil does not split. -/
lemma not_splits_cubicSubQuadratic_of_cubicDiscr_neg
    {a b c u v μ : ℝ}
    (hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) < 0) :
    ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  have hdeg :
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).natDegree ≤ 3 := by
    rw [natDegree_cubicSubQuadratic]
  exact not_splits_of_cubicDiscr_neg_of_natDegree_le_three hdeg hdisc

/-- If the average of the quadratic roots lies strictly above the cubic root
interval, then the midpoint tangent coefficient gives a negative cubic
discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_average_above_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcmean : c < (u + v) / 2) :
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C (3 * ((u + v) / 2) - (a + b + c)) *
          ((X - C u) * (X - C v))) < 0 := by
  exact
    cubicDiscr_cubicSubQuadratic_neg_of_deriv_disc_neg
      (cubicSubQuadratic_average_above_deriv_disc_neg hab hbc hcmean)

/-- Derivative-discriminant non-splitting certificate for the
cubic-minus-quadratic pencil. -/
lemma exists_cubicSubQuadratic_not_splits_of_deriv_disc_neg
    {a b c u v μ : ℝ}
    (hμ : 0 < μ)
    (hderiv :
      (a + b + c + μ) ^ 2 <
        3 * (a * b + a * c + b * c + μ * (u + v))) :
    ∃ ν : ℝ, 0 < ν ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C ν * ((X - C u) * (X - C v))).Splits := by
  refine ⟨μ, hμ, ?_⟩
  exact
    not_splits_cubicSubQuadratic_of_cubicDiscr_neg
      (cubicDiscr_cubicSubQuadratic_neg_of_deriv_disc_neg hderiv)

/-- If the average of the quadratic roots lies strictly above the cubic root
interval, then some positive subtraction coefficient makes the monic
cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_average_above
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcmean : c < (u + v) / 2) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  have hμ : 0 < 3 * ((u + v) / 2) - (a + b + c) := by
    exact cubicSubQuadratic_average_above_mu_pos hab hbc hcmean
  exact
    exists_cubicSubQuadratic_not_splits_of_deriv_disc_neg hμ
      (cubicSubQuadratic_average_above_deriv_disc_neg hab hbc hcmean)

/-- The midpoint tangent coefficient is positive when both quadratic roots lie
strictly above the cubic root interval. -/
lemma cubicSubQuadratic_right_roots_above_mu_pos {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) (huv : u ≤ v) :
    0 < 3 * ((u + v) / 2) - (a + b + c) := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact cubicSubQuadratic_average_above_mu_pos hab hbc hcmean

/-- With the midpoint tangent coefficient, the derivative discriminant of the
cubic-minus-quadratic pencil is negative. -/
lemma cubicSubQuadratic_right_roots_above_deriv_disc_neg {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u) (huv : u ≤ v) :
    (a + b + c + (3 * ((u + v) / 2) - (a + b + c))) ^ 2 <
      3 *
        (a * b + a * c + b * c +
          (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact cubicSubQuadratic_average_above_deriv_disc_neg hab hbc hcmean

/-- If both quadratic roots lie strictly above the cubic roots, then the
midpoint tangent coefficient gives a negative cubic discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_right_roots_above_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u)
    (huv : u ≤ v) :
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C (3 * ((u + v) / 2) - (a + b + c)) *
          ((X - C u) * (X - C v))) < 0 := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact cubicDiscr_cubicSubQuadratic_average_above_neg hab hbc hcmean

/-- If both quadratic roots lie strictly above the cubic roots, then some
positive subtraction coefficient makes the monic cubic-minus-quadratic pencil
fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_right_roots_above
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcu : c < u)
    (huv : u ≤ v) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact exists_cubicSubQuadratic_not_splits_of_average_above hab hbc hcmean

/-- A negative-discriminant subtraction pencil obstructs compatibility of
opposite-sign scalar multiples. -/
lemma not_compatible_scaled_pair_of_opposite_of_sub_not_splits
    {P Q : ℝ[X]} {A B μ : ℝ} (hAB : A * B < 0) (hμ : 0 < μ)
    (hnot_splits : ¬ (P - C μ * Q).Splits) :
    ¬ Compatible (C A * P) (C B * Q) := by
  have hA_ne : A ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).1
  have hB_ne : B ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hAB)).2
  intro hcompat
  rcases lt_or_gt_of_ne hA_ne with hA_neg | hA_pos
  · have hB_pos : 0 < B := by
      by_contra hB_not
      have hB_nonpos : B ≤ 0 := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt hA_neg) hB_nonpos
      linarith
    have hnegA_pos : 0 < -A := by linarith
    have hα : 0 ≤ 1 / (-A) := by positivity
    have hβ : 0 ≤ μ / B := by positivity
    have hcase := hcompat (1 / (-A)) (μ / B) hα hβ
    have hcombo_eq :
        C (1 / (-A)) * (C A * P) + C (μ / B) * (C B * Q) =
          -(P - C μ * Q) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_C]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · have hzero' : P - C μ * Q = 0 := by
        rw [← neg_eq_zero]
        simpa using hzero
      exact hnot_splits (hzero'.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits (by simpa using hsplit.neg)
  · have hB_neg : B < 0 := by
      by_contra hB_not
      have hB_nonneg : 0 ≤ B := le_of_not_gt hB_not
      have hprod_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA_pos) hB_nonneg
      linarith
    have hnegB_pos : 0 < -B := by linarith
    have hα : 0 ≤ 1 / A := by positivity
    have hβ : 0 ≤ μ / (-B) := by positivity
    have hcase := hcompat (1 / A) (μ / (-B)) hα hβ
    have hcombo_eq :
        C (1 / A) * (C A * P) + C (μ / (-B)) * (C B * Q) =
          P - C μ * Q := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_sub, eval_C]
      field_simp [hA_ne, hB_ne]
      ring
    rw [hcombo_eq] at hcase
    rcases hcase with hzero | ⟨_, hsplit⟩
    · exact hnot_splits (hzero.symm ▸ Polynomial.Splits.zero)
    · exact hnot_splits hsplit

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and the average of the quadratic roots lies
strictly above the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_average_above
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcmean : c < (u + v) / 2) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_average_above hab hbc hcmean
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and both quadratic roots lie strictly above
the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_right_roots_above
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcu : c < u) (huv : u ≤ v) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  have hcmean : c < (u + v) / 2 := by nlinarith
  exact
    not_compatible_scaled_cubic_quadratic_of_opposite_of_average_above
      hAB hab hbc hcmean

end LiuOppositeSigns
end RealRooted
