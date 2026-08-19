import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.Average
import RealRooted.LiuOppositeSigns.ForwardLowDegree

/-!
# Liu cubic/quadratic middle-gap obstruction

This module contains the cubic-minus-quadratic obstruction for the branch in
which both quadratic roots lie to the right of the middle cubic root and at
most at the upper cubic root.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

private lemma middle_gap_left_deriv_neg_of_side_nonneg
    {a b c u v : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u < v)
    (hvc : v ≤ c)
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c)) :
    (u - b) * (u - c) + (u - a) * (u - c) +
      (u - a) * (u - b) < 0 := by
  let x : ℝ := b - a
  let y : ℝ := u - b
  let z : ℝ := v - u
  let w : ℝ := c - v
  have hx : 0 ≤ x := by
    dsimp [x]
    linarith
  have hy : 0 < y := by
    dsimp [y]
    linarith
  have hz : 0 < z := by
    dsimp [z]
    linarith
  have hw : 0 ≤ w := by
    dsimp [w]
    linarith
  have hS_gap :
      (a + b + c) * (u + v) - 3 * (u * v) -
          (a * b + a * c + b * c) =
        w * x + 2 * w * y + w * z - x * y - y ^ 2 + z ^ 2 := by
    dsimp [x, y, z, w]
    ring
  have hP_gap :
      (u - b) * (u - c) + (u - a) * (u - c) +
          (u - a) * (u - b) =
        -w * x - 2 * w * y + x * y - x * z + y ^ 2 - 2 * y * z := by
    dsimp [x, y, z, w]
    ring
  rw [hP_gap]
  have hS : 0 ≤ w * x + 2 * w * y + w * z - x * y - y ^ 2 + z ^ 2 := by rwa [hS_gap] at hside
  by_contra hnot
  have hP : 0 ≤ -w * x - 2 * w * y + x * y - x * z + y ^ 2 - 2 * y * z :=
    le_of_not_gt hnot
  have hw_bound : x + 2 * y ≤ w + z := by nlinarith
  have hP_bound : (w + z) * (x + 2 * y) ≤ y * (x + y) := by nlinarith
  have hbig : (x + 2 * y) * (x + 2 * y) ≤ y * (x + y) := by
    nlinarith [mul_le_mul_of_nonneg_right hw_bound (by nlinarith)]
  have hcontra : y * (x + y) < (x + 2 * y) * (x + 2 * y) := by
    nlinarith [sq_nonneg x, mul_nonneg hx (le_of_lt hy),
      sq_pos_of_ne_zero (ne_of_gt hy)]
  nlinarith

private lemma middle_gap_right_deriv_pos_of_side_nonpos
    {a b c u v : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u < v)
    (hvc : v < c)
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) ≤ 0) :
    0 < (v - b) * (v - c) + (v - a) * (v - c) +
      (v - a) * (v - b) := by
  let x : ℝ := b - a
  let y : ℝ := u - b
  let z : ℝ := v - u
  let w : ℝ := c - v
  have hx : 0 ≤ x := by
    dsimp [x]
    linarith
  have hy : 0 < y := by
    dsimp [y]
    linarith
  have hz : 0 < z := by
    dsimp [z]
    linarith
  have hw : 0 < w := by
    dsimp [w]
    linarith
  have hS_gap :
      (a + b + c) * (u + v) - 3 * (u * v) -
          (a * b + a * c + b * c) =
        w * x + 2 * w * y + w * z - x * y - y ^ 2 + z ^ 2 := by
    dsimp [x, y, z, w]
    ring
  have hP_gap :
      (v - b) * (v - c) + (v - a) * (v - c) +
          (v - a) * (v - b) =
        -w * x - 2 * w * y - 2 * w * z + x * y + x * z +
          y ^ 2 + 2 * y * z + z ^ 2 := by
    dsimp [x, y, z, w]
    ring
  rw [hP_gap]
  have hS : w * x + 2 * w * y + w * z - x * y - y ^ 2 + z ^ 2 ≤ 0 := by rwa [hS_gap] at hside
  have hden_pos : 0 < x + 2 * y + z := by positivity
  have hw_upper : w * (x + 2 * y + z) ≤ y * (x + y) - z ^ 2 := by nlinarith
  have htarget_bound :
      y * (x + y) - z ^ 2 <
        (x + 2 * y + 2 * z) * (x + 2 * y + z) := by
    nlinarith [sq_nonneg x, sq_nonneg z, mul_nonneg hx (le_of_lt hy),
      mul_pos hy hz]
  have hw_lt : w < x + 2 * y + 2 * z := by nlinarith
  have hfirst : 0 ≤ y * (x + y) - w * (x + 2 * y + z) - z ^ 2 := by nlinarith
  have hdecomp :
      -w * x - 2 * w * y - 2 * w * z + x * y + x * z +
          y ^ 2 + 2 * y * z + z ^ 2 =
        (y * (x + y) - w * (x + 2 * y + z) - z ^ 2) +
          z * (x + 2 * y + 2 * z - w) := by
    ring
  rw [hdecomp]
  positivity

/-- Tangent-at-`u` coefficient for the middle-gap branch when the side
expression is nonnegative. -/
lemma cubicSubQuadratic_middle_gap_left_tangent_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u < v)
    (hvc : v ≤ c)
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c)) :
    0 <
      ((u - b) * (u - c) + (u - a) * (u - c) +
        (u - a) * (u - b)) / (u - v) := by
  have hnum :
      (u - b) * (u - c) + (u - a) * (u - c) +
        (u - a) * (u - b) < 0 :=
    middle_gap_left_deriv_neg_of_side_nonneg hab hbu huv hvc hside
  exact div_pos_of_neg_of_neg hnum (sub_neg.mpr huv)

/-- Tangent-at-`v` coefficient for the middle-gap branch when the side
expression is nonpositive. -/
lemma cubicSubQuadratic_middle_gap_right_tangent_mu_pos
    {a b c u v : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u < v)
    (hvc : v < c)
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) ≤ 0) :
    0 <
      ((v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b)) / (v - u) := by
  have hnum :
      0 < (v - b) * (v - c) + (v - a) * (v - c) +
        (v - a) * (v - b) :=
    middle_gap_right_deriv_pos_of_side_nonpos hab hbu huv hvc hside
  exact div_pos hnum (sub_pos.mpr huv)

/-- Tangency at the lower quadratic root gives a negative discriminant in the
middle-gap branch when the side expression is nonnegative. -/
lemma cubicDiscr_cubicSubQuadratic_middle_gap_left_tangent_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u < v)
    (hvc : v ≤ c)
    (hside : 0 ≤ (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c)) :
    let μ : ℝ :=
      ((u - b) * (u - c) + (u - a) * (u - c) +
        (u - a) * (u - b)) / (u - v)
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) < 0 := by
  intro μ
  have huv_neg : u - v < 0 := sub_neg.mpr huv
  have huv_ne : u - v ≠ 0 := ne_of_lt huv_neg
  have hcrit :
      3 * u ^ 2 - 2 * (a + b + c + μ) * u +
        (a * b + a * c + b * c + μ * (u + v)) = 0 := by
    dsimp [μ]
    field_simp [huv_ne]
    ring_nf
  let y : ℝ := (u - a) * (u - b) * (u - c)
  have hvalue :
      y =
        (u - a) * (u - b) * (u - c) -
          μ * ((u - u) * (u - v)) := by
    dsimp [y]
    ring
  have hua_pos : 0 < u - a := sub_pos.mpr (lt_of_le_of_lt hab hbu)
  have hub_pos : 0 < u - b := sub_pos.mpr hbu
  have huc_neg : u - c < 0 := sub_neg.mpr (lt_of_lt_of_le huv hvc)
  have hy_neg : y < 0 := by
    dsimp [y]
    exact mul_neg_of_pos_of_neg (mul_pos hua_pos hub_pos) huc_neg
  have hy_ne : y ≠ 0 := ne_of_lt hy_neg
  have hsecond :
      3 * u - (a + b + c + μ) =
        ((a + b + c) * (u + v) - 3 * (u * v) -
          (a * b + a * c + b * c)) / (u - v) := by
    dsimp [μ]
    field_simp [huv_ne]
    ring_nf
  have hsecond_nonpos : 3 * u - (a + b + c + μ) ≤ 0 := by
    rw [hsecond]
    exact div_nonpos_of_nonneg_of_nonpos hside (le_of_lt huv_neg)
  have hsecond_cube_nonpos : (3 * u - (a + b + c + μ)) ^ 3 ≤ 0 := by
    nlinarith [sq_nonneg (3 * u - (a + b + c + μ))]
  have hsign :
      0 ≤ y * (3 * u - (a + b + c + μ)) ^ 3 :=
    mul_nonneg_of_nonpos_of_nonpos (le_of_lt hy_neg) hsecond_cube_nonpos
  exact cubicDiscr_cubicSubQuadratic_neg_of_critical_value hcrit hvalue hy_ne hsign

/-- Tangency at the upper quadratic root gives a negative discriminant in the
middle-gap branch when the side expression is nonpositive. -/
lemma cubicDiscr_cubicSubQuadratic_middle_gap_right_tangent_neg
    {a b c u v : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u < v)
    (hvc : v < c)
    (hside : (a + b + c) * (u + v) - 3 * (u * v) -
      (a * b + a * c + b * c) ≤ 0) :
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
  have hva_pos : 0 < v - a := sub_pos.mpr (lt_of_le_of_lt hab (lt_trans hbu huv))
  have hvb_pos : 0 < v - b := sub_pos.mpr (lt_trans hbu huv)
  have hvc_neg : v - c < 0 := sub_neg.mpr hvc
  have hy_neg : y < 0 := by
    dsimp [y]
    exact mul_neg_of_pos_of_neg (mul_pos hva_pos hvb_pos) hvc_neg
  have hy_ne : y ≠ 0 := ne_of_lt hy_neg
  have hsecond :
      3 * v - (a + b + c + μ) =
        ((a + b + c) * (u + v) - 3 * (u * v) -
          (a * b + a * c + b * c)) / (v - u) := by
    dsimp [μ]
    field_simp [hvu_ne]
    ring_nf
  have hsecond_nonpos : 3 * v - (a + b + c + μ) ≤ 0 := by
    rw [hsecond]
    exact div_nonpos_of_nonpos_of_nonneg hside (le_of_lt hvu_pos)
  have hsecond_cube_nonpos : (3 * v - (a + b + c + μ)) ^ 3 ≤ 0 := by
    nlinarith [sq_nonneg (3 * v - (a + b + c + μ))]
  have hsign :
      0 ≤ y * (3 * v - (a + b + c + μ)) ^ 3 :=
    mul_nonneg_of_nonpos_of_nonpos (le_of_lt hy_neg) hsecond_cube_nonpos
  exact cubicDiscr_cubicSubQuadratic_neg_of_critical_value hcrit hvalue hy_ne hsign

/-- If the upper quadratic root is the upper cubic root and the lower
quadratic root lies strictly to the right of the middle cubic root, cancelling
the common upper root gives a quadratic-minus-linear non-splitting certificate.
-/
lemma exists_cubicSubQuadratic_not_splits_of_middle_gap_upper_endpoint
    {a b c u : ℝ} (hab : a ≤ b) (hbu : b < u) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C c))).Splits := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_quadraticSubLinear_not_splits_of_upper_lt_right_root hab hbu
  refine ⟨μ, hμ, ?_⟩
  intro hsplits
  have hfactor :
      ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C c)) =
        (X - C c) * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C u)) := by
    ring
  exact
    (not_splits_common_factor_sub_of_not_splits
        (X_sub_C_ne_zero c) (Polynomial.Splits.X_sub_C c) hnot_splits)
      (by simpa [hfactor] using hsplits)

/-- If the quadratic has a double root strictly between the middle and upper
cubic roots, the explicit Hessian certificate gives a negative cubic
discriminant.

The witness is easiest after translating `u` to `0`.  The term
`lam ^ 2 / (3 * p)` makes the Hessian value at `0` strictly negative, while
the added `3 * lam ^ 2 + 3` gives uniform positive slack for the Hessian
leading coefficient. -/
private lemma cubicDiscr_cubicSubQuadratic_middle_double_roots_neg
    {a b c u : ℝ} (hab : a ≤ b) (hbu : b < u) (huc : u < c) :
    let sau : ℝ := u - a;
    let sbu : ℝ := u - b;
    let suc : ℝ := c - u;
    let lam : ℝ := sau * sbu - suc * (sau + sbu);
    let p : ℝ := sau * sbu * suc;
    let μ : ℝ := sau + sbu + lam ^ 2 / (3 * p) + 3 * lam ^ 2 + 3;
    cubicDiscr
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C u))) < 0 := by
  intro sau sbu suc lam p μ
  have hsau_pos : 0 < sau := by
    dsimp [sau]
    linarith
  have hsbu_pos : 0 < sbu := by
    dsimp [sbu]
    linarith
  have hsuc_pos : 0 < suc := by
    dsimp [suc]
    linarith
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  let extra : ℝ := suc + lam ^ 2 / (3 * p)
  have hextra_nonneg : 0 ≤ extra := by
    dsimp [extra]
    have hden_pos : 0 < 3 * p := by positivity
    exact add_nonneg (le_of_lt hsuc_pos)
      (div_nonneg (sq_nonneg lam) (le_of_lt hden_pos))
  have htail_disc_pos : 0 < (3 * lam ^ 2 + 3) ^ 2 - 3 * lam := by
    nlinarith only [sq_nonneg (12 * lam - 1), sq_nonneg (lam ^ 2)]
  let β : ℝ := sau + sbu - suc - μ
  have hβ_eq : β = -(extra + (3 * lam ^ 2 + 3)) := by
    dsimp [β, extra, μ]
    ring
  have hlead_eq :
      β ^ 2 - 3 * (1 : ℝ) * lam =
        (extra + (3 * lam ^ 2 + 3)) ^ 2 - 3 * lam := by
    rw [hβ_eq]
    ring
  have hlead : 0 < β ^ 2 - 3 * (1 : ℝ) * lam := by
    rw [hlead_eq]
    have htail_nonneg : 0 ≤ 3 * lam ^ 2 + 3 := by nlinarith only [sq_nonneg lam]
    have hprod_nonneg : 0 ≤ (3 * lam ^ 2 + 3) * extra :=
      mul_nonneg htail_nonneg hextra_nonneg
    have hextra_terms :
        0 ≤ 2 * (3 * lam ^ 2 + 3) * extra + extra ^ 2 := by
      nlinarith only [hprod_nonneg, sq_nonneg extra]
    have hdecomp' (E L : ℝ) :
        (E + (3 * L ^ 2 + 3)) ^ 2 - 3 * L =
          ((3 * L ^ 2 + 3) ^ 2 - 3 * L) +
            (2 * (3 * L ^ 2 + 3) * E + E ^ 2) := by
      ring
    have hdecomp := hdecomp' extra lam
    rw [hdecomp]
    exact add_pos_of_pos_of_nonneg htail_disc_pos hextra_terms
  have hval_eq :
      lam ^ 2 - 3 * β * (-p) = -3 * p * (suc + 3 * lam ^ 2 + 3) := by
    dsimp [β, extra, μ]
    field_simp [hp_ne]
    ring_nf
  have hval_simple : lam ^ 2 - 3 * β * (-p) < 0 := by
    rw [hval_eq]
    have hbracket : 0 < suc + 3 * lam ^ 2 + 3 := by nlinarith only [sq_nonneg lam, hsuc_pos]
    have hprod_pos : 0 < 3 * p * (suc + 3 * lam ^ 2 + 3) :=
      mul_pos (mul_pos (by norm_num) hp_pos) hbracket
    nlinarith only [hprod_pos]
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u))
  have hshift : cubicDiscr P = cubicDiscr (P.comp (X + C u)) := by
    dsimp [P]
    exact (cubicDiscr_cubicSubQuadratic_comp_X_add_C a b c u u μ u).symm
  have hcomp_eq :
      P.comp (X + C u) =
        ((X + C sau) * (X + C sbu) * (X - C suc)) -
          C μ * (X * X) := by
    dsimp [P, sau, sbu, suc]
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_add, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hnorm_poly :
      ((X + C sau) * (X + C sbu) * (X - C suc)) - C μ * (X * X) =
        C 1 * X ^ 3 + C β * X ^ 2 + C lam * X + C (-p) := by
    dsimp [β, lam, p]
    rw [C_neg]
    simp only [C_add, C_mul, C_sub, C_1]
    ring
  have hdisc_norm :
      cubicDiscr
        (((X + C sau) * (X + C sbu) * (X - C suc)) -
          C μ * (X * X)) < 0 := by
    rw [hnorm_poly]
    exact cubicDiscr_neg_of_hessian_neg_at 1 β lam (-p) 0 hlead (by
      simpa using hval_simple)
  change cubicDiscr P < 0
  rw [hshift, hcomp_eq]
  exact hdisc_norm

/-- If the quadratic has a double root strictly between the middle and upper
cubic roots, then some positive subtraction coefficient makes the monic
cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_middle_double_roots
    {a b c u : ℝ} (hab : a ≤ b) (hbu : b < u) (huc : u < c) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C u))).Splits := by
  let sau : ℝ := u - a
  let sbu : ℝ := u - b
  let suc : ℝ := c - u
  let lam : ℝ := sau * sbu - suc * (sau + sbu)
  let p : ℝ := sau * sbu * suc
  let μ : ℝ := sau + sbu + lam ^ 2 / (3 * p) + 3 * lam ^ 2 + 3
  have hsau_pos : 0 < sau := by
    dsimp [sau]
    linarith
  have hsbu_pos : 0 < sbu := by
    dsimp [sbu]
    linarith
  have hsuc_pos : 0 < suc := by
    dsimp [suc]
    linarith
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hμ : 0 < μ := by
    dsimp [μ]
    have hden_pos : 0 < 3 * p := by positivity
    have hfrac_nonneg : 0 ≤ lam ^ 2 / (3 * p) :=
      div_nonneg (sq_nonneg lam) (le_of_lt hden_pos)
    nlinarith [hsau_pos, hsbu_pos, hfrac_nonneg, sq_nonneg lam]
  refine ⟨μ, hμ, ?_⟩
  have hdisc :
      cubicDiscr
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C u))) < 0 := by
    dsimp [μ, p, lam, sau, sbu, suc]
    exact cubicDiscr_cubicSubQuadratic_middle_double_roots_neg
      hab hbu huc
  exact not_splits_cubicSubQuadratic_of_cubicDiscr_neg hdisc

/-- In the distinct-root middle-gap branch, some positive subtraction
coefficient makes the monic cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_middle_gap_distinct
    {a b c u v : ℝ} (hab : a ≤ b) (_hbc : b ≤ c) (hbu : b < u)
    (huv : u < v) (hvc : v ≤ c) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases hvc_lt : v < c
  · let S : ℝ :=
      (a + b + c) * (u + v) - 3 * (u * v) -
        (a * b + a * c + b * c)
    rcases le_total 0 S with hside | hside
    · let μ : ℝ :=
        ((u - b) * (u - c) + (u - a) * (u - c) +
          (u - a) * (u - b)) / (u - v)
      have hμ : 0 < μ := by
        dsimp [μ]
        exact cubicSubQuadratic_middle_gap_left_tangent_mu_pos
          hab hbu huv hvc (by simpa [S] using hside)
      refine ⟨μ, hμ, ?_⟩
      have hdisc :
          cubicDiscr
            (((X - C a) * (X - C b) * (X - C c)) -
              C μ * ((X - C u) * (X - C v))) < 0 := by
        dsimp [μ]
        exact cubicDiscr_cubicSubQuadratic_middle_gap_left_tangent_neg
          hab hbu huv hvc (by simpa [S] using hside)
      exact not_splits_cubicSubQuadratic_of_cubicDiscr_neg hdisc
    · let μ : ℝ :=
        ((v - b) * (v - c) + (v - a) * (v - c) +
          (v - a) * (v - b)) / (v - u)
      have hμ : 0 < μ := by
        dsimp [μ]
        exact cubicSubQuadratic_middle_gap_right_tangent_mu_pos
          hab hbu huv hvc_lt (by simpa [S] using hside)
      refine ⟨μ, hμ, ?_⟩
      have hdisc :
          cubicDiscr
            (((X - C a) * (X - C b) * (X - C c)) -
              C μ * ((X - C u) * (X - C v))) < 0 := by
        dsimp [μ]
        exact cubicDiscr_cubicSubQuadratic_middle_gap_right_tangent_neg
          hab hbu huv hvc_lt (by simpa [S] using hside)
      exact not_splits_cubicSubQuadratic_of_cubicDiscr_neg hdisc
  · have hvc_eq : v = c := le_antisymm hvc (le_of_not_gt hvc_lt)
    subst v
    exact exists_cubicSubQuadratic_not_splits_of_middle_gap_upper_endpoint
      hab hbu

/-- In the middle-gap branch, some positive subtraction coefficient makes the
monic cubic-minus-quadratic pencil fail to split. -/
lemma exists_cubicSubQuadratic_not_splits_of_middle_gap
    {a b c u v : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hbu : b < u)
    (huv : u ≤ v) (hvc : v ≤ c) :
    ∃ μ : ℝ, 0 < μ ∧
      ¬ (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases huv_lt : u < v
  · exact exists_cubicSubQuadratic_not_splits_of_middle_gap_distinct
      hab hbc hbu huv_lt hvc
  · have hvu : v ≤ u := le_of_not_gt huv_lt
    have huv_eq : u = v := le_antisymm huv hvu
    subst v
    by_cases huc_lt : u < c
    · exact exists_cubicSubQuadratic_not_splits_of_middle_double_roots
        hab hbu huc_lt
    · have huc : u ≤ c := hvc
      have huc_eq : u = c := le_antisymm huc (le_of_not_gt huc_lt)
      subst u
      exact exists_cubicSubQuadratic_not_splits_of_middle_gap_upper_endpoint
        hab hbu

/-- The cubic/quadratic endpoint is not compatible in the distinct-root
middle-gap branch. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_middle_gap_distinct
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hbu : b < u) (huv : u < v) (hvc : v ≤ c) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_middle_gap_distinct
      hab hbc hbu huv hvc
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

/-- The cubic/quadratic endpoint is not compatible in the middle-gap branch. -/
lemma not_compatible_scaled_cubic_quadratic_of_opposite_of_middle_gap
    {a b c u v A B : ℝ} (hAB : A * B < 0) (hab : a ≤ b) (hbc : b ≤ c)
    (hbu : b < u) (huv : u ≤ v) (hvc : v ≤ c) :
    ¬ Compatible
      (C A * ((X - C a) * (X - C b) * (X - C c)))
      (C B * ((X - C u) * (X - C v))) := by
  obtain ⟨μ, hμ, hnot_splits⟩ :=
    exists_cubicSubQuadratic_not_splits_of_middle_gap
      hab hbc hbu huv hvc
  exact
    not_compatible_scaled_pair_of_opposite_of_sub_not_splits
      (P := (X - C a) * (X - C b) * (X - C c))
      (Q := (X - C u) * (X - C v))
      hAB hμ hnot_splits

end LiuOppositeSigns
end RealRooted
