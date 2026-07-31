import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.Average

/-!
# Liu cubic/quadratic strict lower-side obstruction

This module contains the strict distinct-root lower-side
cubic-minus-quadratic obstruction branch used in the degree-three/two forward
direction of Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Tangent-at-`v` coefficient for the strict lower-side cubic/quadratic
obstruction. -/
lemma cubicSubQuadratic_left_roots_below_strict_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hva : v < a) :
    0 <
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u) := by
  have hva_neg : v - a < 0 := sub_neg.mpr hva
  have hvb_neg : v - b < 0 := sub_neg.mpr (lt_of_lt_of_le hva hab)
  have hvc_neg : v - c < 0 := sub_neg.mpr (lt_of_lt_of_le hva (hab.trans hbc))
  have h1 : 0 < (v - b) * (v - c) := mul_pos_of_neg_of_neg hvb_neg hvc_neg
  have h2 : 0 < (v - a) * (v - c) := mul_pos_of_neg_of_neg hva_neg hvc_neg
  have h3 : 0 < (v - a) * (v - b) := mul_pos_of_neg_of_neg hva_neg hvb_neg
  have hnum :
      0 < (v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b) := by
    linarith
  exact div_pos hnum (sub_pos.mpr huv)

/-- If the two quadratic roots are strictly below the cubic root interval and
distinct, tangent at the upper quadratic root gives a negative cubic
discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_left_roots_below_strict_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hva : v < a) :
    let μ : ℝ :=
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) < 0 := by
  intro μ
  have hvu_pos : 0 < v - u := sub_pos.mpr huv
  have hvu_ne : v - u ≠ 0 := ne_of_gt hvu_pos
  have hcrit :
      3 * v ^ 2 - 2 * (a + b + c + μ) * v +
        (a * b + a * c + b * c + μ * (u + v)) = 0 := by
    dsimp [μ]
    field_simp [hvu_ne]
    ring_nf
  let y : ℝ := (v - a) * (v - b) * (v - c)
  have hvalue :
      y =
        (v - a) * (v - b) * (v - c) -
          μ * ((v - u) * (v - v)) := by
    dsimp [y]
    ring
  have hμ_pos : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_left_roots_below_strict_mu_pos hab hbc huv hva
  have hva_neg : v - a < 0 := sub_neg.mpr hva
  have hvb_neg : v - b < 0 := sub_neg.mpr (lt_of_lt_of_le hva hab)
  have hvc_neg : v - c < 0 := sub_neg.mpr (lt_of_lt_of_le hva (hab.trans hbc))
  have hy_neg : y < 0 := by
    dsimp [y]
    exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hva_neg hvb_neg) hvc_neg
  have hy_ne : y ≠ 0 := ne_of_lt hy_neg
  have hsecond_nonpos : 3 * v - (a + b + c + μ) ≤ 0 := by
    have hsecond_neg : 3 * v - (a + b + c + μ) < 0 := by
      nlinarith
    exact le_of_lt hsecond_neg
  have hsecond_cube_nonpos : (3 * v - (a + b + c + μ)) ^ 3 ≤ 0 := by
    nlinarith [sq_nonneg (3 * v - (a + b + c + μ))]
  have hsign :
      0 ≤ y * (3 * v - (a + b + c + μ)) ^ 3 :=
    mul_nonneg_of_nonpos_of_nonpos (le_of_lt hy_neg) hsecond_cube_nonpos
  exact cubicDiscr_cubicSubQuadratic_neg_of_critical_value hcrit hvalue hy_ne hsign

/-- If the two distinct quadratic roots lie strictly below the cubic roots, then
some positive subtraction coefficient makes the monic cubic-minus-quadratic
pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_left_roots_below_strict
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hva : v < a) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  let μ : ℝ :=
    ((v - b) * (v - c) + (v - a) * (v - c) +
      (v - a) * (v - b)) / (v - u)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_left_roots_below_strict_mu_pos hab hbc huv hva
  refine ⟨μ, hμ, ?_⟩
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_left_roots_below_strict_neg
      hab hbc huv hva
  exact not_splits_cubicSubQuadratic_of_cubicDiscr_neg hdisc

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and the two distinct quadratic roots lie
strictly below the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below_strict
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u < v) (hva : v < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_left_roots_below_strict
      hab hbc huv hva
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

end LiuOppositeSigns
end RealRooted
