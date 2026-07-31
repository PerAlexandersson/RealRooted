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

private def cubicSubQuadraticLeftBelowStrictBracket
    (duv sav dab dbc : ℝ) : ℝ :=
  4 * dab ^ 6 + 12 * dab ^ 5 * dbc + 24 * dab ^ 5 * duv +
    48 * dab ^ 5 * sav + 12 * dab ^ 4 * dbc ^ 2 +
    60 * dab ^ 4 * dbc * duv + 120 * dab ^ 4 * dbc * sav +
    48 * dab ^ 4 * duv ^ 2 + 228 * dab ^ 4 * duv * sav +
    228 * dab ^ 4 * sav ^ 2 + 4 * dab ^ 3 * dbc ^ 3 +
    48 * dab ^ 3 * dbc ^ 2 * duv + 96 * dab ^ 3 * dbc ^ 2 * sav +
    96 * dab ^ 3 * dbc * duv ^ 2 + 456 * dab ^ 3 * dbc * duv * sav +
    456 * dab ^ 3 * dbc * sav ^ 2 + 32 * dab ^ 3 * duv ^ 3 +
    336 * dab ^ 3 * duv ^ 2 * sav + 816 * dab ^ 3 * duv * sav ^ 2 +
    544 * dab ^ 3 * sav ^ 3 + 12 * dab ^ 2 * dbc ^ 3 * duv +
    24 * dab ^ 2 * dbc ^ 3 * sav + 60 * dab ^ 2 * dbc ^ 2 * duv ^ 2 +
    276 * dab ^ 2 * dbc ^ 2 * duv * sav +
    276 * dab ^ 2 * dbc ^ 2 * sav ^ 2 + 48 * dab ^ 2 * dbc * duv ^ 3 +
    504 * dab ^ 2 * dbc * duv ^ 2 * sav +
    1224 * dab ^ 2 * dbc * duv * sav ^ 2 +
    816 * dab ^ 2 * dbc * sav ^ 3 + 171 * dab ^ 2 * duv ^ 3 * sav +
    828 * dab ^ 2 * duv ^ 2 * sav ^ 2 +
    1368 * dab ^ 2 * duv * sav ^ 3 + 684 * dab ^ 2 * sav ^ 4 +
    12 * dab * dbc ^ 3 * duv ^ 2 + 48 * dab * dbc ^ 3 * duv * sav +
    48 * dab * dbc ^ 3 * sav ^ 2 + 24 * dab * dbc ^ 2 * duv ^ 3 +
    216 * dab * dbc ^ 2 * duv ^ 2 * sav +
    504 * dab * dbc ^ 2 * duv * sav ^ 2 +
    336 * dab * dbc ^ 2 * sav ^ 3 + 171 * dab * dbc * duv ^ 3 * sav +
    828 * dab * dbc * duv ^ 2 * sav ^ 2 +
    1368 * dab * dbc * duv * sav ^ 3 + 684 * dab * dbc * sav ^ 4 +
    270 * dab * duv ^ 3 * sav ^ 2 + 864 * dab * duv ^ 2 * sav ^ 3 +
    1080 * dab * duv * sav ^ 4 + 432 * dab * sav ^ 5 +
    4 * dbc ^ 3 * duv ^ 3 + 24 * dbc ^ 3 * duv ^ 2 * sav +
    48 * dbc ^ 3 * duv * sav ^ 2 + 32 * dbc ^ 3 * sav ^ 3 +
    36 * dbc ^ 2 * duv ^ 3 * sav +
    180 * dbc ^ 2 * duv ^ 2 * sav ^ 2 +
    288 * dbc ^ 2 * duv * sav ^ 3 + 144 * dbc ^ 2 * sav ^ 4 +
    135 * dbc * duv ^ 3 * sav ^ 2 + 432 * dbc * duv ^ 2 * sav ^ 3 +
    540 * dbc * duv * sav ^ 4 + 216 * dbc * sav ^ 5 +
    135 * duv ^ 3 * sav ^ 3 + 324 * duv ^ 2 * sav ^ 4 +
    324 * duv * sav ^ 5 + 108 * sav ^ 6

private lemma cubicSubQuadraticLeftBelowStrictBracket_pos
    {duv sav dab dbc : ℝ} (hduv : 0 < duv) (hsav : 0 < sav)
    (hdab : 0 ≤ dab) (hdbc : 0 ≤ dbc) :
    0 < cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc := by
  dsimp [cubicSubQuadraticLeftBelowStrictBracket]
  positivity

/-- Normalized gap-coordinate discriminant identity for the strict lower-side
cubic/quadratic obstruction. -/
private lemma cubicDiscr_cubicSubQuadratic_left_roots_below_strict_norm
    (duv sav dab dbc : ℝ) (hduv_ne : duv ≠ 0) :
    let μ : ℝ :=
      (dab ^ 2 + dab * dbc + 4 * dab * sav + 2 * dbc * sav +
        3 * sav ^ 2) / duv
    cubicDiscr
      (((X - C (duv + sav)) * (X - C (duv + sav + dab)) *
          (X - C (duv + sav + dab + dbc))) -
        C μ * ((X - C 0) * (X - C duv))) =
      -(sav * (dab + sav) * (dab + dbc + sav) *
        cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc / duv ^ 3) := by
  intro μ
  have hpoly :
      ((X - C (duv + sav)) * (X - C (duv + sav + dab)) *
            (X - C (duv + sav + dab + dbc)) -
          C μ * ((X - C 0) * (X - C duv))) =
        C 1 * X ^ 3 +
          C ((-(dab ^ 2) - dab * dbc - 2 * dab * duv - 4 * dab * sav -
              dbc * duv - 2 * dbc * sav - 3 * duv ^ 2 - 3 * duv * sav -
              3 * sav ^ 2) / duv) * X ^ 2 +
          C (2 * dab ^ 2 + 2 * dab * dbc + 4 * dab * duv + 8 * dab * sav +
              2 * dbc * duv + 4 * dbc * sav + 3 * duv ^ 2 + 6 * duv * sav +
              6 * sav ^ 2) * X +
          C (-(dab ^ 2 * duv) - dab ^ 2 * sav - dab * dbc * duv -
              dab * dbc * sav - 2 * dab * duv ^ 2 - 4 * dab * duv * sav -
              2 * dab * sav ^ 2 - dbc * duv ^ 2 - 2 * dbc * duv * sav -
              dbc * sav ^ 2 - duv ^ 3 - 3 * duv ^ 2 * sav -
              3 * duv * sav ^ 2 - sav ^ 3) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    dsimp [μ]
    field_simp [hduv_ne]
    ring_nf
  rw [hpoly, cubicDiscr_of_coeffs]
  dsimp [cubicSubQuadraticLeftBelowStrictBracket]
  field_simp [hduv_ne]
  ring_nf

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
  let duv : ℝ := v - u
  let sav : ℝ := a - v
  let dab : ℝ := b - a
  let dbc : ℝ := c - b
  have hduv_ne : duv ≠ 0 := ne_of_gt (by dsimp [duv]; linarith)
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hshift : cubicDiscr P = cubicDiscr (P.comp (X + C u)) := by
    dsimp [P]
    exact (cubicDiscr_cubicSubQuadratic_comp_X_add_C a b c u v μ u).symm
  have hcomp_eq :
      P.comp (X + C u) =
        ((X - C (duv + sav)) * (X - C (duv + sav + dab)) *
            (X - C (duv + sav + dab + dbc))) -
          C ((dab ^ 2 + dab * dbc + 4 * dab * sav + 2 * dbc * sav +
              3 * sav ^ 2) / duv) * ((X - C 0) * (X - C duv)) := by
    dsimp [P]
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    dsimp [μ, duv, sav, dab, dbc]
    field_simp [hduv_ne]
    ring_nf
  have hdisc_eq :
      cubicDiscr P =
        -(sav * (dab + sav) * (dab + dbc + sav) *
          cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc / duv ^ 3) := by
    rw [hshift, hcomp_eq]
    exact cubicDiscr_cubicSubQuadratic_left_roots_below_strict_norm
      duv sav dab dbc hduv_ne
  change cubicDiscr P < 0
  rw [hdisc_eq]
  have hduv_pos : 0 < duv := by
    dsimp [duv]
    linarith
  have hsav_pos : 0 < sav := by
    dsimp [sav]
    linarith
  have hdab_nonneg : 0 ≤ dab := by
    dsimp [dab]
    linarith
  have hdbc_nonneg : 0 ≤ dbc := by
    dsimp [dbc]
    linarith
  have hbracket : 0 < cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc :=
    cubicSubQuadraticLeftBelowStrictBracket_pos hduv_pos hsav_pos
      hdab_nonneg hdbc_nonneg
  have hnum :
      0 <
        sav * (dab + sav) * (dab + dbc + sav) *
          cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc := by
    positivity
  have hfrac :
      0 <
        sav * (dab + sav) * (dab + dbc + sav) *
          cubicSubQuadraticLeftBelowStrictBracket duv sav dab dbc / duv ^ 3 :=
    div_pos hnum (by positivity)
  nlinarith

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
