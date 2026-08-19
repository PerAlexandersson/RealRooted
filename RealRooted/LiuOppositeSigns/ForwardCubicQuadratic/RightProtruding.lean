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

/-- In the right-protruding branch with `u ≤ a`, the tangent side expression is
automatically nonnegative. -/
lemma cubicSubQuadratic_right_protruding_left_below_side_nonneg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u ≤ a)
    (hcv : c < v) :
    0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) := by
  let dab : ℝ := b - a
  let dbc : ℝ := c - b
  let sau : ℝ := a - u
  let dcv : ℝ := v - c
  have hdab : 0 ≤ dab := by
    dsimp [dab]
    linarith
  have hdbc : 0 ≤ dbc := by
    dsimp [dbc]
    linarith
  have hsau : 0 ≤ sau := by
    dsimp [sau]
    linarith
  have hdcv : 0 ≤ dcv := by
    dsimp [dcv]
    linarith
  have hside :
      (a + b + c) * (u + v) - 3 * (u * v) -
          (a * b + a * c + b * c) =
        dab ^ 2 + 2 * dab * dbc + dab * sau + 2 * dab * dcv +
          dbc ^ 2 + 2 * dbc * sau + dbc * dcv + 3 * sau * dcv := by
    dsimp [dab, dbc, sau, dcv]
    ring
  rw [hside]
  positivity

/-! ## Tangency-at-`v` branch

The following certificate extends the right-protruding obstruction beyond the
`u ≤ a` branch.  It uses the critical-value form of the cubic discriminant:
the chosen coefficient makes `v` a critical point of the cubic-minus-quadratic
pencil, while `P(v) > 0` and the side inequality below makes this critical
point a weak positive local minimum.
-/

/-- Tangency-at-`v` negative-discriminant certificate for the right-protruding
branch. -/
lemma cubicDiscr_cubicSubQuadratic_right_protruding_tangent_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hcv : c < v)
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
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
  have hsecond_nonneg :
      0 ≤ 3 * v - (a + b + c + μ) := by
    rw [hsecond]
    exact div_nonneg hside (le_of_lt hvu_pos)
  have hsign :
      0 ≤ y * (3 * v - (a + b + c + μ)) ^ 3 :=
    mul_nonneg (le_of_lt hy_pos) (pow_nonneg hsecond_nonneg 3)
  exact cubicDiscr_cubicSubQuadratic_neg_of_critical_value hcrit hvalue hy_ne hsign

/-! ## Midpoint negative-side branch -/

/-- The midpoint subtraction coefficient is positive in the negative-side
right-protruding branch. -/
lemma cubicSubQuadratic_right_protruding_midpoint_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcv : c < v)
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) < 0) :
    0 < 3 * ((u + v) / 2) - (a + b + c) := by
  let e1 : ℝ := a + b + c
  let e2 : ℝ := a * b + a * c + b * c
  let G : ℝ := e1 ^ 2 - 3 * e2
  have hG_nonneg : 0 ≤ G := by
    dsimp [G, e1, e2]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hv_pos : 0 < 3 * v - e1 := by
    dsimp [e1]
    nlinarith
  have hprod_eq :
      (3 * u - e1) * (3 * v - e1) =
        G - 3 * ((a + b + c) * (u + v) - 3 * (u * v) -
          (a * b + a * c + b * c)) := by
    dsimp [G, e1, e2]
    ring
  have hprod_pos : 0 < (3 * u - e1) * (3 * v - e1) := by
    rw [hprod_eq]
    nlinarith
  have hu_pos : 0 < 3 * u - e1 := by nlinarith [hprod_pos, hv_pos]
  dsimp [e1] at hu_pos hv_pos ⊢
  nlinarith

/-- In the negative-side right-protruding branch, the midpoint coefficient
makes the derivative discriminant of the cubic-minus-quadratic pencil
negative. -/
lemma cubicSubQuadratic_right_protruding_midpoint_deriv_disc_neg
    {a b c u v : ℝ}
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) < 0) :
    (a + b + c + (3 * ((u + v) / 2) - (a + b + c))) ^ 2 <
      3 * (a * b + a * c + b * c +
        (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) := by
  have hdelta :
      4 *
          (3 * (a * b + a * c + b * c +
              (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) -
            (a + b + c + (3 * ((u + v) / 2) - (a + b + c))) ^ 2) =
        9 * (v - u) ^ 2 -
          12 * ((a + b + c) * (u + v) - 3 * (u * v) -
            (a * b + a * c + b * c)) := by
    ring
  have hdelta_pos :
      0 <
        3 * (a * b + a * c + b * c +
            (3 * ((u + v) / 2) - (a + b + c)) * (u + v)) -
          (a + b + c + (3 * ((u + v) / 2) - (a + b + c))) ^ 2 := by
    nlinarith [sq_nonneg (v - u), hdelta]
  nlinarith

/-- In the negative-side right-protruding branch, some positive subtraction
coefficient makes the monic cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_right_protruding_side_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcv : c < v)
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) < 0) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  let μ : ℝ := 3 * ((u + v) / 2) - (a + b + c)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_right_protruding_midpoint_mu_pos
      hab hbc hcv hside
  exact
    exists_cubicSubQuadratic_not_splits_of_deriv_disc_neg hμ
      (by
        dsimp [μ]
        exact cubicSubQuadratic_right_protruding_midpoint_deriv_disc_neg hside)

/-- The cubic/quadratic endpoint is not compatible in the negative-side
right-protruding branch. -/
lemma
    not_compatible_scaled_cubic_quadratic_of_opposite_of_right_protruding_side_neg
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hcv : c < v)
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) < 0) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_right_protruding_side_neg
      hab hbc hcv hside
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

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
  have huv : u < v :=
    lt_of_le_of_lt (hua.trans (hab.trans hbc)) hcv
  have hside :
      0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
        (a * b + a * c + b * c) :=
    cubicSubQuadratic_right_protruding_left_below_side_nonneg hab hbc hua hcv
  exact
    cubicDiscr_cubicSubQuadratic_right_protruding_tangent_neg
      hab hbc huv hcv hside

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

/-- In the tangent-at-`v` right-protruding branch, some positive subtraction
coefficient makes the monic cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_right_protruding_tangent
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (huv : u < v)
    (hcv : c < v)
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
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
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
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
