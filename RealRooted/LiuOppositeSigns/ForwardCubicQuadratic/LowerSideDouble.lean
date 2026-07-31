import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.LowerSideStrict

/-!
# Liu cubic/quadratic double-root lower-side obstruction

This module contains the double-root lower-side cubic-minus-quadratic
obstruction branch and the combined weak-lower-side endpoint wrapper used in
the degree-three/two forward direction of Liu Theorem 2.1.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Tangent coefficient for the lower-side cubic/quadratic obstruction when
the quadratic has a double root. -/
lemma cubicSubQuadratic_left_double_roots_below_mu_pos
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    0 < (b - u) * (c - u) / (a - u) := by
  have hau : 0 < a - u := sub_pos.mpr hua
  have hbu : 0 < b - u := sub_pos.mpr (lt_of_lt_of_le hua hab)
  have hcu : 0 < c - u := sub_pos.mpr (lt_of_lt_of_le hua (hab.trans hbc))
  exact div_pos (mul_pos hbu hcu) hau

private def cubicSubQuadraticLeftDoubleBelowBracket
    (sav dab dbc : ℝ) : ℝ :=
  3 * dab ^ 8 + 31 * sav ^ 8 + 3 * dab ^ 4 * dbc ^ 4 +
    12 * dab ^ 7 * dbc + 12 * dab ^ 5 * dbc ^ 3 +
    16 * dbc ^ 4 * sav ^ 4 + 18 * dab ^ 6 * dbc ^ 2 +
    40 * dab ^ 7 * sav + 72 * dbc ^ 3 * sav ^ 5 +
    106 * dbc * sav ^ 7 + 131 * dbc ^ 2 * sav ^ 6 +
    212 * dab * sav ^ 7 + 216 * dab ^ 6 * sav ^ 2 +
    612 * dab ^ 5 * sav ^ 3 + 624 * dab ^ 2 * sav ^ 6 +
    1014 * dab ^ 4 * sav ^ 4 + 1024 * dab ^ 3 * sav ^ 5 +
    20 * dab ^ 3 * dbc ^ 4 * sav + 48 * dab * dbc ^ 4 * sav ^ 3 +
    48 * dab ^ 2 * dbc ^ 4 * sav ^ 2 +
    100 * dab ^ 4 * dbc ^ 3 * sav + 140 * dab ^ 6 * dbc * sav +
    180 * dab ^ 5 * dbc ^ 2 * sav + 296 * dab * dbc ^ 3 * sav ^ 4 +
    312 * dab ^ 3 * dbc ^ 3 * sav ^ 2 +
    450 * dab ^ 2 * dbc ^ 3 * sav ^ 3 +
    624 * dab * dbc * sav ^ 6 + 648 * dab ^ 5 * dbc * sav ^ 2 +
    656 * dab * dbc ^ 2 * sav ^ 5 +
    696 * dab ^ 4 * dbc ^ 2 * sav ^ 2 +
    1310 * dab ^ 2 * dbc ^ 2 * sav ^ 4 +
    1320 * dab ^ 3 * dbc ^ 2 * sav ^ 3 +
    1530 * dab ^ 4 * dbc * sav ^ 3 +
    1536 * dab ^ 2 * dbc * sav ^ 5 +
    2028 * dab ^ 3 * dbc * sav ^ 4

private lemma cubicSubQuadraticLeftDoubleBelowBracket_pos
    {sav dab dbc : ℝ} (hsav : 0 < sav) (hdab : 0 ≤ dab) (hdbc : 0 ≤ dbc) :
    0 < cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc := by
  dsimp [cubicSubQuadraticLeftDoubleBelowBracket]
  positivity

/-- Normalized gap-coordinate discriminant identity for the lower-side
cubic/quadratic obstruction with a double quadratic root. -/
private lemma cubicDiscr_cubicSubQuadratic_left_double_roots_below_norm
    (sav dab dbc : ℝ) (hsav_ne : sav ≠ 0) :
    let μ : ℝ := (sav + dab) * (sav + dab + dbc) / sav
    cubicDiscr
      (((X - C sav) * (X - C (sav + dab)) *
          (X - C (sav + dab + dbc))) -
        C μ * ((X - C 0) * (X - C 0))) =
      -(cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc / sav ^ 2) := by
  intro μ
  have hpoly :
      ((X - C sav) * (X - C (sav + dab)) *
            (X - C (sav + dab + dbc)) -
          C μ * ((X - C 0) * (X - C 0))) =
        C 1 * X ^ 3 +
          C ((-(dab ^ 2) - dab * dbc - 4 * dab * sav -
              2 * dbc * sav - 4 * sav ^ 2) / sav) * X ^ 2 +
          C (dab ^ 2 + dab * dbc + 4 * dab * sav + 2 * dbc * sav +
              3 * sav ^ 2) * X +
          C (-(dab ^ 2 * sav) - dab * dbc * sav - 2 * dab * sav ^ 2 -
              dbc * sav ^ 2 - sav ^ 3) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    dsimp [μ]
    field_simp [hsav_ne]
    ring_nf
  rw [hpoly, cubicDiscr_of_coeffs]
  dsimp [cubicSubQuadraticLeftDoubleBelowBracket]
  field_simp [hsav_ne]
  ring_nf

/-- If the quadratic has a double root strictly below the cubic root interval,
then the tangent coefficient gives a negative cubic discriminant. -/
lemma cubicDiscr_cubicSubQuadratic_left_double_roots_below_neg
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    let μ : ℝ := (b - u) * (c - u) / (a - u)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C u))) < 0 := by
  intro μ
  let sav : ℝ := a - u
  let dab : ℝ := b - a
  let dbc : ℝ := c - b
  have hsav_ne : sav ≠ 0 := ne_of_gt (by dsimp [sav]; linarith)
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u))
  have hshift : cubicDiscr P = cubicDiscr (P.comp (X + C u)) := by
    dsimp [P]
    exact (cubicDiscr_cubicSubQuadratic_comp_X_add_C a b c u u μ u).symm
  have hcomp_eq :
      P.comp (X + C u) =
        ((X - C sav) * (X - C (sav + dab)) *
            (X - C (sav + dab + dbc))) -
          C ((sav + dab) * (sav + dab + dbc) / sav) *
            ((X - C 0) * (X - C 0)) := by
    dsimp [P]
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    dsimp [μ, sav, dab, dbc]
    field_simp [hsav_ne]
    ring_nf
  have hdisc_eq :
      cubicDiscr P =
        -(cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc / sav ^ 2) := by
    rw [hshift, hcomp_eq]
    exact cubicDiscr_cubicSubQuadratic_left_double_roots_below_norm
      sav dab dbc hsav_ne
  change cubicDiscr P < 0
  rw [hdisc_eq]
  have hsav_pos : 0 < sav := by
    dsimp [sav]
    linarith
  have hdab_nonneg : 0 ≤ dab := by
    dsimp [dab]
    linarith
  have hdbc_nonneg : 0 ≤ dbc := by
    dsimp [dbc]
    linarith
  have hbracket : 0 < cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc :=
    cubicSubQuadraticLeftDoubleBelowBracket_pos hsav_pos hdab_nonneg hdbc_nonneg
  have hfrac :
      0 < cubicSubQuadraticLeftDoubleBelowBracket sav dab dbc / sav ^ 2 :=
    div_pos hbracket (by positivity)
  nlinarith

/-- If the quadratic has a double root strictly below the cubic roots, then
some positive subtraction coefficient makes the monic cubic-minus-quadratic
pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_left_double_roots_below
    {a b c u : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hua : u < a) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C u))).Splits := by
  let μ : ℝ := (b - u) * (c - u) / (a - u)
  have hμ : 0 < μ := by
    dsimp [μ]
    exact cubicSubQuadratic_left_double_roots_below_mu_pos hab hbc hua
  refine ⟨μ, hμ, ?_⟩
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C u))) < 0 := by
    dsimp [μ]
    exact cubicDiscr_cubicSubQuadratic_left_double_roots_below_neg hab hbc hua
  exact not_splits_cubicSubQuadratic_of_cubicDiscr_neg hdisc

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and the quadratic has a double root strictly
below the cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_left_double_roots_below
    {a b c u A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hua : u < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C u))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_left_double_roots_below hab hbc hua
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C u))
      hAB hμ hnot_splits

/-- The cubic/quadratic endpoint is not compatible when the leading
coefficients have opposite signs and both quadratic roots lie weakly below the
cubic root interval. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hva : v < a) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  by_cases huv_lt : u < v
  · exact
      not_compatible_scaled_cubic_quadratic_of_opposite_of_left_roots_below_strict
        hAB hab hbc huv_lt hva
  · have hvu : v ≤ u := le_of_not_gt huv_lt
    have huv_eq : u = v := le_antisymm huv hvu
    subst v
    exact
      not_compatible_scaled_cubic_quadratic_of_opposite_of_left_double_roots_below
        hAB hab hbc hva

end LiuOppositeSigns
end RealRooted
