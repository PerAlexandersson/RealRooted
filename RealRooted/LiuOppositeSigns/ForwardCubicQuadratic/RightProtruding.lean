import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.Average

/-!
# Liu cubic/quadratic right-protruding obstruction

This module contains the right-protruding cubic-minus-quadratic obstruction
branch used in the degree-three/two forward direction of Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Tangent-at-`v` coefficient for the right-protruding branch where the lower
quadratic root lies weakly below the cubic root interval. -/
lemma cubicSubQuadratic_right_protruding_left_below_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u ≤ a)
    (hcv : c < v) :
    0 <
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u) := by
  have hvb_pos : 0 < v - b := sub_pos.mpr (lt_of_le_of_lt hbc hcv)
  have hvc_pos : 0 < v - c := sub_pos.mpr hcv
  have hva_pos : 0 < v - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcv)
  have hvu_pos : 0 < v - u :=
    sub_pos.mpr (lt_of_le_of_lt (hua.trans (hab.trans hbc)) hcv)
  have hnum :
      0 < (v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b) := by
    positivity
  exact div_pos hnum hvu_pos

/-- The tangent-at-`v` coefficient is positive whenever `u < v` and `v` lies
strictly above the cubic root interval. -/
lemma cubicSubQuadratic_right_protruding_tangent_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hcv : c < v) :
    0 <
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u) := by
  have hvb_pos : 0 < v - b := sub_pos.mpr (lt_of_le_of_lt hbc hcv)
  have hvc_pos : 0 < v - c := sub_pos.mpr hcv
  have hva_pos : 0 < v - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcv)
  have hvu_pos : 0 < v - u := sub_pos.mpr huv
  have hnum :
      0 < (v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b) := by
    positivity
  exact div_pos hnum hvu_pos

private def cubicSubQuadraticRightProtrudingLeftBelowBracket
    (sau dab dbc dcv : ℝ) : ℝ :=
  4 * dab ^ 6 + 24 * dab ^ 5 * dbc + 24 * dab ^ 5 * dcv +
    12 * dab ^ 5 * sau + 60 * dab ^ 4 * dbc ^ 2 +
    135 * dab ^ 4 * dbc * dcv + 72 * dab ^ 4 * dbc * sau +
    75 * dab ^ 4 * dcv ^ 2 + 84 * dab ^ 4 * dcv * sau +
    12 * dab ^ 4 * sau ^ 2 + 80 * dab ^ 3 * dbc ^ 3 +
    300 * dab ^ 3 * dbc ^ 2 * dcv +
    168 * dab ^ 3 * dbc ^ 2 * sau +
    360 * dab ^ 3 * dbc * dcv ^ 2 +
    441 * dab ^ 3 * dbc * dcv * sau +
    72 * dab ^ 3 * dbc * sau ^ 2 + 140 * dab ^ 3 * dcv ^ 3 +
    273 * dab ^ 3 * dcv ^ 2 * sau +
    96 * dab ^ 3 * dcv * sau ^ 2 + 4 * dab ^ 3 * sau ^ 3 +
    60 * dab ^ 2 * dbc ^ 4 + 330 * dab ^ 2 * dbc ^ 3 * dcv +
    192 * dab ^ 2 * dbc ^ 3 * sau +
    642 * dab ^ 2 * dbc ^ 2 * dcv ^ 2 +
    795 * dab ^ 2 * dbc ^ 2 * dcv * sau +
    156 * dab ^ 2 * dbc ^ 2 * sau ^ 2 +
    534 * dab ^ 2 * dbc * dcv ^ 3 +
    990 * dab ^ 2 * dbc * dcv ^ 2 * sau +
    477 * dab ^ 2 * dbc * dcv * sau ^ 2 +
    24 * dab ^ 2 * dbc * sau ^ 3 + 162 * dab ^ 2 * dcv ^ 4 +
    387 * dab ^ 2 * dcv ^ 3 * sau +
    333 * dab ^ 2 * dcv ^ 2 * sau ^ 2 +
    36 * dab ^ 2 * dcv * sau ^ 3 + 24 * dab * dbc ^ 5 +
    180 * dab * dbc ^ 4 * dcv + 108 * dab * dbc ^ 4 * sau +
    504 * dab * dbc ^ 3 * dcv ^ 2 +
    603 * dab * dbc ^ 3 * dcv * sau +
    144 * dab * dbc ^ 3 * sau ^ 2 +
    672 * dab * dbc ^ 2 * dcv ^ 3 +
    1125 * dab * dbc ^ 2 * dcv ^ 2 * sau +
    666 * dab * dbc ^ 2 * dcv * sau ^ 2 +
    48 * dab * dbc ^ 2 * sau ^ 3 + 432 * dab * dbc * dcv ^ 4 +
    873 * dab * dbc * dcv ^ 3 * sau +
    900 * dab * dbc * dcv ^ 2 * sau ^ 2 +
    171 * dab * dbc * dcv * sau ^ 3 + 108 * dab * dcv ^ 5 +
    243 * dab * dcv ^ 4 * sau + 378 * dab * dcv ^ 3 * sau ^ 2 +
    135 * dab * dcv ^ 2 * sau ^ 3 + 4 * dbc ^ 6 +
    39 * dbc ^ 5 * dcv + 24 * dbc ^ 5 * sau +
    147 * dbc ^ 4 * dcv ^ 2 + 165 * dbc ^ 4 * dcv * sau +
    48 * dbc ^ 4 * sau ^ 2 + 274 * dbc ^ 3 * dcv ^ 3 +
    420 * dbc ^ 3 * dcv ^ 2 * sau +
    273 * dbc ^ 3 * dcv * sau ^ 2 + 32 * dbc ^ 3 * sau ^ 3 +
    270 * dbc ^ 2 * dcv ^ 4 + 522 * dbc ^ 2 * dcv ^ 3 * sau +
    495 * dbc ^ 2 * dcv ^ 2 * sau ^ 2 +
    171 * dbc ^ 2 * dcv * sau ^ 3 + 135 * dbc * dcv ^ 5 +
    324 * dbc * dcv ^ 4 * sau + 351 * dbc * dcv ^ 3 * sau ^ 2 +
    270 * dbc * dcv ^ 2 * sau ^ 3 + 27 * dcv ^ 6 +
    81 * dcv ^ 5 * sau + 81 * dcv ^ 4 * sau ^ 2 +
    135 * dcv ^ 3 * sau ^ 3

private lemma cubicSubQuadraticRightProtrudingLeftBelowBracket_pos
    {sau dab dbc dcv : ℝ} (hsau : 0 ≤ sau) (hdab : 0 ≤ dab)
    (hdbc : 0 ≤ dbc) (hdcv : 0 < dcv) :
    0 < cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv := by
  dsimp [cubicSubQuadraticRightProtrudingLeftBelowBracket]
  positivity

/-- Normalized gap-coordinate discriminant identity for the right-protruding
cubic/quadratic obstruction with lower quadratic root below the cubic interval.
-/
private lemma cubicDiscr_cubicSubQuadratic_right_protruding_left_below_norm
    (sau dab dbc dcv : ℝ) (hden_ne : sau + dab + dbc + dcv ≠ 0) :
    let μ : ℝ :=
      (dab * dbc + 2 * dab * dcv + dbc ^ 2 + 4 * dbc * dcv + 3 * dcv ^ 2) /
        (sau + dab + dbc + dcv)
    cubicDiscr
      (((X - C sau) * (X - C (sau + dab)) *
          (X - C (sau + dab + dbc))) -
        C μ * ((X - C 0) * (X - C (sau + dab + dbc + dcv)))) =
      -(dcv * (dbc + dcv) * (dab + dbc + dcv) *
        cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv /
          (sau + dab + dbc + dcv) ^ 3) := by
  intro μ
  have hpoly :
      ((X - C sau) * (X - C (sau + dab)) *
            (X - C (sau + dab + dbc)) -
          C μ * ((X - C 0) * (X - C (sau + dab + dbc + dcv)))) =
        C 1 * X ^ 3 +
          C (-(2 * dab ^ 2 + 4 * dab * dbc + 4 * dab * dcv +
              5 * dab * sau + 2 * dbc ^ 2 + 5 * dbc * dcv +
              4 * dbc * sau + 3 * dcv ^ 2 + 3 * dcv * sau +
              3 * sau ^ 2) / (sau + dab + dbc + dcv)) * X ^ 2 +
          C (dab ^ 2 + 2 * dab * dbc + 2 * dab * dcv + 4 * dab * sau +
              dbc ^ 2 + 4 * dbc * dcv + 2 * dbc * sau + 3 * dcv ^ 2 +
              3 * sau ^ 2) * X +
          C (-(sau * (dab + sau) * (dab + dbc + sau))) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    dsimp [μ]
    field_simp [hden_ne]
    ring_nf
  rw [hpoly, cubicDiscr_of_coeffs]
  dsimp [cubicSubQuadraticRightProtrudingLeftBelowBracket]
  field_simp [hden_ne]
  ring_nf

/-- If the upper quadratic root lies strictly above the cubic root interval and
the lower quadratic root lies weakly below the lower cubic root, then
tangent at the upper quadratic root gives a negative cubic discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_right_protruding_left_below_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u ≤ a)
    (hcv : c < v) :
    let μ : ℝ :=
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) < 0 := by
  intro μ
  let sau : ℝ := a - u
  let dab : ℝ := b - a
  let dbc : ℝ := c - b
  let dcv : ℝ := v - c
  have hden_pos : 0 < sau + dab + dbc + dcv := by
    dsimp [sau, dab, dbc, dcv]
    linarith
  have hden_ne : sau + dab + dbc + dcv ≠ 0 := ne_of_gt hden_pos
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hshift : cubicDiscr P = cubicDiscr (P.comp (X + C u)) := by
    dsimp [P]
    exact (cubicDiscr_cubicSubQuadratic_comp_X_add_C a b c u v μ u).symm
  have hcomp_eq :
      P.comp (X + C u) =
        ((X - C sau) * (X - C (sau + dab)) *
            (X - C (sau + dab + dbc))) -
          C ((dab * dbc + 2 * dab * dcv + dbc ^ 2 + 4 * dbc * dcv +
              3 * dcv ^ 2) / (sau + dab + dbc + dcv)) *
            ((X - C 0) * (X - C (sau + dab + dbc + dcv))) := by
    dsimp [P]
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    dsimp [μ, sau, dab, dbc, dcv]
    field_simp [hden_ne]
    ring_nf
  have hdisc_eq :
      cubicDiscr P =
        -(dcv * (dbc + dcv) * (dab + dbc + dcv) *
          cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv /
            (sau + dab + dbc + dcv) ^ 3) := by
    rw [hshift, hcomp_eq]
    exact cubicDiscr_cubicSubQuadratic_right_protruding_left_below_norm
      sau dab dbc dcv hden_ne
  change cubicDiscr P < 0
  rw [hdisc_eq]
  have hsau_nonneg : 0 ≤ sau := by
    dsimp [sau]
    linarith
  have hdab_nonneg : 0 ≤ dab := by
    dsimp [dab]
    linarith
  have hdbc_nonneg : 0 ≤ dbc := by
    dsimp [dbc]
    linarith
  have hdcv_pos : 0 < dcv := by
    dsimp [dcv]
    linarith
  have hbracket :
      0 < cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv :=
    cubicSubQuadraticRightProtrudingLeftBelowBracket_pos
      hsau_nonneg hdab_nonneg hdbc_nonneg hdcv_pos
  have hnum :
      0 <
        dcv * (dbc + dcv) * (dab + dbc + dcv) *
          cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv := by
    positivity
  have hfrac :
      0 <
        dcv * (dbc + dcv) * (dab + dbc + dcv) *
          cubicSubQuadraticRightProtrudingLeftBelowBracket sau dab dbc dcv /
            (sau + dab + dbc + dcv) ^ 3 :=
    div_pos hnum (by positivity)
  nlinarith

/-- In the right-protruding branch where the lower quadratic root lies weakly
below the cubic interval, some positive subtraction coefficient makes the
monic cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_right_protruding_left_below
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u ≤ a)
    (hcv : c < v) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  let μ : ℝ :=
    ((v - b) * (v - c) + (v - a) * (v - c) +
      (v - a) * (v - b)) / (v - u)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_right_protruding_left_below_mu_pos
      hab hbc hua hcv
  refine ⟨μ, hμ, ?_⟩
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_right_protruding_left_below_neg
      hab hbc hua hcv
  exact not_splits_cubicSubQuadratic_of_cubicDiscr_neg hdisc

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs, the lower quadratic root lies weakly below
the cubic interval, and the upper quadratic root lies strictly above it. -/
lemma
    not_compatible_scaled_cubic_quadratic_of_opposite_of_right_protruding_left_below
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u ≤ a) (hcv : c < v) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_right_protruding_left_below
      hab hbc hua hcv
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

/-! ## Tangency-at-`v` branch

The following certificate extends the right-protruding obstruction beyond the
`u ≤ a` branch.  It uses the critical-value form of the cubic discriminant:
the chosen coefficient makes `v` a critical point of the cubic-minus-quadratic
pencil, while `P(v) > 0` and the side inequality below makes this critical
point a positive local minimum.
-/

/-- Tangency-at-`v` negative-discriminant certificate for the right-protruding
branch. -/
lemma cubicDiscr_cubicSubQuadratic_right_protruding_tangent_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hcv : c < v)
    (hside : 0 < (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c)) :
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
  have hsecond :
      3 * v - (a + b + c + μ) =
        ((a + b + c) * (u + v) - 3 * (u * v) -
          (a * b + a * c + b * c)) / (v - u) := by
    dsimp [μ]
    field_simp [hvu_ne]
    ring_nf
  have hvb_pos : 0 < v - b := sub_pos.mpr (lt_of_le_of_lt hbc hcv)
  have hvc_pos : 0 < v - c := sub_pos.mpr hcv
  have hva_pos : 0 < v - a := sub_pos.mpr (lt_of_le_of_lt (hab.trans hbc) hcv)
  have hy_pos : 0 < y := by
    dsimp [y]
    positivity
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hsecond_pos :
      0 < 3 * v - (a + b + c + μ) := by
    rw [hsecond]
    exact div_pos hside hvu_pos
  have hsign :
      0 ≤ y * (3 * v - (a + b + c + μ)) ^ 3 :=
    le_of_lt (mul_pos hy_pos (pow_pos hsecond_pos 3))
  exact cubicDiscr_cubicSubQuadratic_neg_of_critical_value hcrit hvalue hy_ne hsign

/-- In the tangent-at-`v` right-protruding branch, some positive subtraction
coefficient makes the monic cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_right_protruding_tangent
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hcv : c < v)
    (hside : 0 < (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c)) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  let μ : ℝ :=
    ((v - b) * (v - c) + (v - a) * (v - c) +
      (v - a) * (v - b)) / (v - u)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_right_protruding_tangent_mu_pos hab hbc huv hcv
  refine ⟨μ, hμ, ?_⟩
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_right_protruding_tangent_neg
      hab hbc huv hcv hside
  exact not_splits_cubicSubQuadratic_of_cubicDiscr_neg hdisc

/-- The cubic/quadratic endpoint is not compatible in the tangent-at-`v`
right-protruding branch. -/
lemma
    not_compatible_scaled_cubic_quadratic_of_opposite_of_right_protruding_tangent
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u < v) (hcv : c < v)
    (hside : 0 < (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c)) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_right_protruding_tangent
      hab hbc huv hcv hside
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

end LiuOppositeSigns
end RealRooted
