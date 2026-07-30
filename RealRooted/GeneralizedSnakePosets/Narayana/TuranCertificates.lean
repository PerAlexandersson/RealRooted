import RealRooted.GeneralizedSnakePosets.Narayana.Turan

/-!
# Finite Turan certificates for modified Narayana polynomials

This module contains the explicit checked finite-range Narayana Turan
certificates used while the all-`m` analytic proof is being formalized.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- Explicit `m = 1` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_one (r : ℝ) :
    modifiedNarayanaTuran 1 r = -r := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_zero,
    modifiedNarayanaPolynomial_one, modifiedNarayanaPolynomial_eq_coeffPolynomial 2,
    modifiedNarayanaCoeffPolynomial_two]
  norm_num
  ring

/-- Explicit `m = 2` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_two (r : ℝ) :
    modifiedNarayanaTuran 2 r = -r * (r ^ 2 + r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_one,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 2,
    modifiedNarayanaCoeffPolynomial_two,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 3,
    modifiedNarayanaCoeffPolynomial_three]
  norm_num
  ring

/-- Explicit `m = 3` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_three (r : ℝ) :
    modifiedNarayanaTuran 3 r =
      -r * (r ^ 4 + 3 * r ^ 3 + 6 * r ^ 2 + 3 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 2,
    modifiedNarayanaCoeffPolynomial_two,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 3,
    modifiedNarayanaCoeffPolynomial_three,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 4,
    modifiedNarayanaCoeffPolynomial_four]
  norm_num
  ring

/-- Explicit `m = 4` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_four (r : ℝ) :
    modifiedNarayanaTuran 4 r =
      -r * (r ^ 6 + 6 * r ^ 5 + 21 * r ^ 4 + 28 * r ^ 3 +
        21 * r ^ 2 + 6 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 3,
    modifiedNarayanaCoeffPolynomial_three,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 4,
    modifiedNarayanaCoeffPolynomial_four,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 5,
    modifiedNarayanaCoeffPolynomial_five]
  norm_num
  ring

/-- Explicit `m = 5` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_five (r : ℝ) :
    modifiedNarayanaTuran 5 r =
      -r * (r ^ 8 + 10 * r ^ 7 + 55 * r ^ 6 + 136 * r ^ 5 +
        190 * r ^ 4 + 136 * r ^ 3 + 55 * r ^ 2 + 10 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 4,
    modifiedNarayanaCoeffPolynomial_four,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 5,
    modifiedNarayanaCoeffPolynomial_five,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 6,
    modifiedNarayanaCoeffPolynomial_six]
  norm_num
  ring

/-- Explicit `m = 6` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_six (r : ℝ) :
    modifiedNarayanaTuran 6 r =
      -r * (r ^ 10 + 15 * r ^ 9 + 120 * r ^ 8 + 470 * r ^ 7 +
        1065 * r ^ 6 + 1377 * r ^ 5 + 1065 * r ^ 4 + 470 * r ^ 3 +
          120 * r ^ 2 + 15 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 5,
    modifiedNarayanaCoeffPolynomial_five,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 6,
    modifiedNarayanaCoeffPolynomial_six,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 7,
    modifiedNarayanaCoeffPolynomial_seven]
  norm_num
  ring

/-- Explicit `m = 7` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_seven (r : ℝ) :
    modifiedNarayanaTuran 7 r =
      -r * (r ^ 12 + 21 * r ^ 11 + 231 * r ^ 10 + 1309 * r ^ 9 +
        4389 * r ^ 8 + 8877 * r ^ 7 + 11242 * r ^ 6 + 8877 * r ^ 5 +
          4389 * r ^ 4 + 1309 * r ^ 3 + 231 * r ^ 2 + 21 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 6,
    modifiedNarayanaCoeffPolynomial_six,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 7,
    modifiedNarayanaCoeffPolynomial_seven,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 8,
    modifiedNarayanaCoeffPolynomial_eight]
  norm_num
  ring

/-- Explicit `m = 8` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_eight (r : ℝ) :
    modifiedNarayanaTuran 8 r =
      -r * (r ^ 14 + 28 * r ^ 13 + 406 * r ^ 12 + 3136 * r ^ 11 +
        14602 * r ^ 10 + 42448 * r ^ 9 + 79849 * r ^ 8 +
          98296 * r ^ 7 + 79849 * r ^ 6 + 42448 * r ^ 5 +
            14602 * r ^ 4 + 3136 * r ^ 3 + 406 * r ^ 2 + 28 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 7,
    modifiedNarayanaCoeffPolynomial_seven,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 8,
    modifiedNarayanaCoeffPolynomial_eight,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 9,
    modifiedNarayanaCoeffPolynomial_nine]
  norm_num
  ring

/-- Explicit `m = 9` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_nine (r : ℝ) :
    modifiedNarayanaTuran 9 r =
      -r * (r ^ 16 + 36 * r ^ 15 + 666 * r ^ 14 + 6720 * r ^ 13 +
        41496 * r ^ 12 + 163800 * r ^ 11 + 428610 * r ^ 10 +
          757276 * r ^ 9 + 914706 * r ^ 8 + 757276 * r ^ 7 +
            428610 * r ^ 6 + 163800 * r ^ 5 + 41496 * r ^ 4 +
              6720 * r ^ 3 + 666 * r ^ 2 + 36 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 8,
    modifiedNarayanaCoeffPolynomial_eight,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 9,
    modifiedNarayanaCoeffPolynomial_nine,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 10,
    modifiedNarayanaCoeffPolynomial_ten]
  norm_num
  ring

/-- Explicit `m = 10` Narayana Turan determinant. -/
theorem modifiedNarayanaTuran_ten (r : ℝ) :
    modifiedNarayanaTuran 10 r =
      -r * (r ^ 18 + 45 * r ^ 17 + 1035 * r ^ 16 + 13212 * r ^ 15 +
        104490 * r ^ 14 + 537516 * r ^ 13 + 1866690 * r ^ 12 +
          4475340 * r ^ 11 + 7522164 * r ^ 10 + 8934770 * r ^ 9 +
            7522164 * r ^ 8 + 4475340 * r ^ 7 + 1866690 * r ^ 6 +
              537516 * r ^ 5 + 104490 * r ^ 4 + 13212 * r ^ 3 +
                1035 * r ^ 2 + 45 * r + 1) := by
  rw [modifiedNarayanaTuran, modifiedNarayanaPolynomial_eq_coeffPolynomial 9,
    modifiedNarayanaCoeffPolynomial_nine,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 10,
    modifiedNarayanaCoeffPolynomial_ten,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 11,
    modifiedNarayanaCoeffPolynomial_eleven]
  norm_num
  ring

private theorem modifiedNarayanaTuran_two_factor_nonneg (r : ℝ) :
    0 ≤ r ^ 2 + r + 1 := by
  have hs : 0 ≤ (2 * r + 1) ^ 2 := sq_nonneg (2 * r + 1)
  nlinarith

private theorem modifiedNarayanaTuran_three_factor_nonneg_of_nonpos
    {r : ℝ} (hr : r ≤ 0) :
    0 ≤ r ^ 4 + 3 * r ^ 3 + 6 * r ^ 2 + 3 * r + 1 := by
  let y : ℝ := -r
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hdecomp :
      y ^ 4 - 3 * y ^ 3 + 6 * y ^ 2 - 3 * y + 1 =
        (y ^ 2 - (3 / 2) * y + 1) ^ 2 + (7 / 4) * y ^ 2 := by
    ring
  have hnonneg : 0 ≤ y ^ 4 - 3 * y ^ 3 + 6 * y ^ 2 - 3 * y + 1 := by
    rw [hdecomp]
    positivity
  have hrewrite :
      r ^ 4 + 3 * r ^ 3 + 6 * r ^ 2 + 3 * r + 1 =
        y ^ 4 - 3 * y ^ 3 + 6 * y ^ 2 - 3 * y + 1 := by
    dsimp [y]
    ring
  rwa [hrewrite]

private theorem modifiedNarayanaTuran_four_factor_nonneg (r : ℝ) :
    0 ≤ r ^ 6 + 6 * r ^ 5 + 21 * r ^ 4 + 28 * r ^ 3 +
      21 * r ^ 2 + 6 * r + 1 := by
  let y : ℝ := -r
  have hquad : 0 ≤ 3 * y ^ 2 - 4 * y + 3 := by
    have hs : 0 ≤ (3 * y - 2) ^ 2 := sq_nonneg (3 * y - 2)
    nlinarith
  have hdecomp :
      y ^ 6 - 6 * y ^ 5 + 21 * y ^ 4 - 28 * y ^ 3 +
        21 * y ^ 2 - 6 * y + 1 =
          (y - 1) ^ 6 + 2 * y ^ 2 * (3 * y ^ 2 - 4 * y + 3) := by
    ring
  have hnonneg :
      0 ≤ y ^ 6 - 6 * y ^ 5 + 21 * y ^ 4 - 28 * y ^ 3 +
        21 * y ^ 2 - 6 * y + 1 := by
    rw [hdecomp]
    positivity
  have hrewrite :
      r ^ 6 + 6 * r ^ 5 + 21 * r ^ 4 + 28 * r ^ 3 +
        21 * r ^ 2 + 6 * r + 1 =
      y ^ 6 - 6 * y ^ 5 + 21 * y ^ 4 - 28 * y ^ 3 +
        21 * y ^ 2 - 6 * y + 1 := by
    dsimp [y]
    ring
  rwa [hrewrite]

private theorem modifiedNarayanaTuran_five_factor_nonneg_of_nonpos
    {r : ℝ} (hr : r ≤ 0) :
    0 ≤ r ^ 8 + 10 * r ^ 7 + 55 * r ^ 6 + 136 * r ^ 5 +
      190 * r ^ 4 + 136 * r ^ 3 + 55 * r ^ 2 + 10 * r + 1 := by
  let y : ℝ := -r
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hdecomp :
      y ^ 8 - 10 * y ^ 7 + 55 * y ^ 6 - 136 * y ^ 5 +
        190 * y ^ 4 - 136 * y ^ 3 + 55 * y ^ 2 - 10 * y + 1 =
          ((y - 1) ^ 2 * (y ^ 2 - 3 * y + 1)) ^ 2 +
            14 * y ^ 2 * (y - 1) ^ 4 +
              10 * y ^ 3 * (y - 1) ^ 2 + 10 * y ^ 4 := by
    ring
  have hnonneg :
      0 ≤ y ^ 8 - 10 * y ^ 7 + 55 * y ^ 6 - 136 * y ^ 5 +
        190 * y ^ 4 - 136 * y ^ 3 + 55 * y ^ 2 - 10 * y + 1 := by
    rw [hdecomp]
    positivity
  have hrewrite :
      r ^ 8 + 10 * r ^ 7 + 55 * r ^ 6 + 136 * r ^ 5 +
        190 * r ^ 4 + 136 * r ^ 3 + 55 * r ^ 2 + 10 * r + 1 =
      y ^ 8 - 10 * y ^ 7 + 55 * y ^ 6 - 136 * y ^ 5 +
        190 * y ^ 4 - 136 * y ^ 3 + 55 * y ^ 2 - 10 * y + 1 := by
    dsimp [y]
    ring
  rwa [hrewrite]

private theorem modifiedNarayanaTuran_six_factor_nonneg_of_nonpos
    {r : ℝ} (hr : r ≤ 0) :
    0 ≤ r ^ 10 + 15 * r ^ 9 + 120 * r ^ 8 + 470 * r ^ 7 +
      1065 * r ^ 6 + 1377 * r ^ 5 + 1065 * r ^ 4 + 470 * r ^ 3 +
        120 * r ^ 2 + 15 * r + 1 := by
  let y : ℝ := -r
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hdecomp :
      y ^ 10 - 15 * y ^ 9 + 120 * y ^ 8 - 470 * y ^ 7 +
        1065 * y ^ 6 - 1377 * y ^ 5 + 1065 * y ^ 4 - 470 * y ^ 3 +
          120 * y ^ 2 - 15 * y + 1 =
        (y - 1) ^ 6 * (((y - 1) ^ 2 - (5 / 2) * y) ^ 2) +
          (115 / 4) * y ^ 2 * (y - 1) ^ 6 +
            50 * y ^ 4 * (y - 1) ^ 2 + 25 * y ^ 5 := by
    ring
  have hnonneg :
      0 ≤ y ^ 10 - 15 * y ^ 9 + 120 * y ^ 8 - 470 * y ^ 7 +
        1065 * y ^ 6 - 1377 * y ^ 5 + 1065 * y ^ 4 - 470 * y ^ 3 +
          120 * y ^ 2 - 15 * y + 1 := by
    rw [hdecomp]
    positivity
  have hrewrite :
      r ^ 10 + 15 * r ^ 9 + 120 * r ^ 8 + 470 * r ^ 7 +
        1065 * r ^ 6 + 1377 * r ^ 5 + 1065 * r ^ 4 + 470 * r ^ 3 +
          120 * r ^ 2 + 15 * r + 1 =
      y ^ 10 - 15 * y ^ 9 + 120 * y ^ 8 - 470 * y ^ 7 +
        1065 * y ^ 6 - 1377 * y ^ 5 + 1065 * y ^ 4 - 470 * y ^ 3 +
          120 * y ^ 2 - 15 * y + 1 := by
    dsimp [y]
    ring
  rwa [hrewrite]

private theorem modifiedNarayanaTuran_seven_factor_nonneg_of_nonpos
    {r : ℝ} (hr : r ≤ 0) :
    0 ≤ r ^ 12 + 21 * r ^ 11 + 231 * r ^ 10 + 1309 * r ^ 9 +
      4389 * r ^ 8 + 8877 * r ^ 7 + 11242 * r ^ 6 + 8877 * r ^ 5 +
        4389 * r ^ 4 + 1309 * r ^ 3 + 231 * r ^ 2 + 21 * r + 1 := by
  let y : ℝ := -r
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hdecomp :
      y ^ 12 - 21 * y ^ 11 + 231 * y ^ 10 - 1309 * y ^ 9 +
        4389 * y ^ 8 - 8877 * y ^ 7 + 11242 * y ^ 6 - 8877 * y ^ 5 +
          4389 * y ^ 4 - 1309 * y ^ 3 + 231 * y ^ 2 - 21 * y + 1 =
        ((y - 1) ^ 4 * ((y - 1) ^ 2 - (9 / 2) * y)) ^ 2 +
          (219 / 4) * y ^ 2 * (y - 1) ^ 4 *
            (((y - 1) ^ 2 - (56 / 73) * y) ^ 2) +
          (7 / 73) * (1854 * y ^ 4 * (y - 1) ^ 4 +
            1095 * y ^ 5 * (y - 1) ^ 2 + 730 * y ^ 6) := by
    ring
  have hnonneg :
      0 ≤ y ^ 12 - 21 * y ^ 11 + 231 * y ^ 10 - 1309 * y ^ 9 +
        4389 * y ^ 8 - 8877 * y ^ 7 + 11242 * y ^ 6 - 8877 * y ^ 5 +
          4389 * y ^ 4 - 1309 * y ^ 3 + 231 * y ^ 2 - 21 * y + 1 := by
    rw [hdecomp]
    positivity
  have hrewrite :
      r ^ 12 + 21 * r ^ 11 + 231 * r ^ 10 + 1309 * r ^ 9 +
        4389 * r ^ 8 + 8877 * r ^ 7 + 11242 * r ^ 6 + 8877 * r ^ 5 +
          4389 * r ^ 4 + 1309 * r ^ 3 + 231 * r ^ 2 + 21 * r + 1 =
      y ^ 12 - 21 * y ^ 11 + 231 * y ^ 10 - 1309 * y ^ 9 +
        4389 * y ^ 8 - 8877 * y ^ 7 + 11242 * y ^ 6 - 8877 * y ^ 5 +
          4389 * y ^ 4 - 1309 * y ^ 3 + 231 * y ^ 2 - 21 * y + 1 := by
    dsimp [y]
    ring
  rwa [hrewrite]

private theorem modifiedNarayanaTuran_eight_factor_nonneg_of_nonpos
    {r : ℝ} (hr : r ≤ 0) :
    0 ≤ r ^ 14 + 28 * r ^ 13 + 406 * r ^ 12 + 3136 * r ^ 11 +
      14602 * r ^ 10 + 42448 * r ^ 9 + 79849 * r ^ 8 +
        98296 * r ^ 7 + 79849 * r ^ 6 + 42448 * r ^ 5 +
          14602 * r ^ 4 + 3136 * r ^ 3 + 406 * r ^ 2 + 28 * r + 1 := by
  let y : ℝ := -r
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith
  have hdecomp :
      y ^ 14 - 28 * y ^ 13 + 406 * y ^ 12 - 3136 * y ^ 11 +
        14602 * y ^ 10 - 42448 * y ^ 9 + 79849 * y ^ 8 -
          98296 * y ^ 7 + 79849 * y ^ 6 - 42448 * y ^ 5 +
            14602 * y ^ 4 - 3136 * y ^ 3 + 406 * y ^ 2 - 28 * y + 1 =
        (y - 1) ^ 6 *
          (((y - 1) ^ 4 - 7 * y * (y - 1) ^ 2 + 27 * y ^ 2) ^ 2) +
            44 * y ^ 2 * (y - 1) ^ 10 + 153 * y ^ 4 * (y - 1) ^ 6 +
              490 * y ^ 6 * (y - 1) ^ 2 + 196 * y ^ 7 := by
    ring
  have hnonneg :
      0 ≤ y ^ 14 - 28 * y ^ 13 + 406 * y ^ 12 - 3136 * y ^ 11 +
        14602 * y ^ 10 - 42448 * y ^ 9 + 79849 * y ^ 8 -
          98296 * y ^ 7 + 79849 * y ^ 6 - 42448 * y ^ 5 +
            14602 * y ^ 4 - 3136 * y ^ 3 + 406 * y ^ 2 - 28 * y + 1 := by
    rw [hdecomp]
    positivity
  have hrewrite :
      r ^ 14 + 28 * r ^ 13 + 406 * r ^ 12 + 3136 * r ^ 11 +
        14602 * r ^ 10 + 42448 * r ^ 9 + 79849 * r ^ 8 +
          98296 * r ^ 7 + 79849 * r ^ 6 + 42448 * r ^ 5 +
            14602 * r ^ 4 + 3136 * r ^ 3 + 406 * r ^ 2 + 28 * r + 1 =
      y ^ 14 - 28 * y ^ 13 + 406 * y ^ 12 - 3136 * y ^ 11 +
        14602 * y ^ 10 - 42448 * y ^ 9 + 79849 * y ^ 8 -
          98296 * y ^ 7 + 79849 * y ^ 6 - 42448 * y ^ 5 +
            14602 * y ^ 4 - 3136 * y ^ 3 + 406 * y ^ 2 - 28 * y + 1 := by
    dsimp [y]
    ring
  rwa [hrewrite]

private theorem modifiedNarayanaTuran_nine_transformed_factor_nonneg (v : ℝ) :
    0 ≤ v ^ 8 - 20 * v ^ 7 + 266 * v ^ 6 - 1148 * v ^ 5 +
      3360 * v ^ 4 - 2352 * v ^ 3 + 2940 * v ^ 2 + 1176 * v + 588 := by
  have hdecomp :
      v ^ 8 - 20 * v ^ 7 + 266 * v ^ 6 - 1148 * v ^ 5 +
        3360 * v ^ 4 - 2352 * v ^ 3 + 2940 * v ^ 2 + 1176 * v + 588 =
        588 *
          (1 + v - (8059 / 7644) * v ^ 2 + (2375 / 21168) * v ^ 3 +
            (559 / 1278018) * v ^ 4) ^ 2 +
        (46694 / 13) *
          (v - (291119 / 1680984) * v ^ 2 -
            (86493199 / 2029788180) * v ^ 3 +
            (19184581 / 7510216266) * v ^ 4) ^ 2 +
        (159769489038269393 / 57629746006560) *
          (v ^ 2 -
            (93426791103082372 / 479308467114808179) * v ^ 3 +
            (12790840764280841548 / 3848367682464794869191) * v ^ 4) ^ 2 +
        (243852006959300583608529908710229 /
          1846865516450460747919609780800) *
          (v ^ 3 -
            (1607585201352741202316838932575720 /
              27067572772482364780546819866835419) * v ^ 4) ^ 2 +
        (11306893397925665688751978983484359800681357958037 /
          23551765777081102859540771379530264103278272832865) *
          (v ^ 4) ^ 2 := by
    ring
  rw [hdecomp]
  positivity

private theorem modifiedNarayanaTuran_nine_factor_nonneg_of_nonpos
    {r : ℝ} (hr : r ≤ 0) :
    0 ≤ r ^ 16 + 36 * r ^ 15 + 666 * r ^ 14 + 6720 * r ^ 13 +
      41496 * r ^ 12 + 163800 * r ^ 11 + 428610 * r ^ 10 +
        757276 * r ^ 9 + 914706 * r ^ 8 + 757276 * r ^ 7 +
          428610 * r ^ 6 + 163800 * r ^ 5 + 41496 * r ^ 4 +
            6720 * r ^ 3 + 666 * r ^ 2 + 36 * r + 1 := by
  let y : ℝ := -r
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    linarith
  by_cases hy_zero : y = 0
  · have hr_zero : r = 0 := by
      dsimp [y] at hy_zero
      linarith
    rw [hr_zero]
    norm_num
  · have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy_zero)
    let v : ℝ := (y - 1) ^ 2 / y
    have hrewrite_y :
        y ^ 16 - 36 * y ^ 15 + 666 * y ^ 14 - 6720 * y ^ 13 +
          41496 * y ^ 12 - 163800 * y ^ 11 + 428610 * y ^ 10 -
            757276 * y ^ 9 + 914706 * y ^ 8 - 757276 * y ^ 7 +
              428610 * y ^ 6 - 163800 * y ^ 5 + 41496 * y ^ 4 -
                6720 * y ^ 3 + 666 * y ^ 2 - 36 * y + 1 =
          y ^ 8 * (v ^ 8 - 20 * v ^ 7 + 266 * v ^ 6 - 1148 * v ^ 5 +
            3360 * v ^ 4 - 2352 * v ^ 3 + 2940 * v ^ 2 + 1176 * v + 588) := by
      dsimp [v]
      field_simp [hy_pos.ne']
      ring
    have hnonneg_y :
        0 ≤ y ^ 16 - 36 * y ^ 15 + 666 * y ^ 14 - 6720 * y ^ 13 +
          41496 * y ^ 12 - 163800 * y ^ 11 + 428610 * y ^ 10 -
            757276 * y ^ 9 + 914706 * y ^ 8 - 757276 * y ^ 7 +
              428610 * y ^ 6 - 163800 * y ^ 5 + 41496 * y ^ 4 -
                6720 * y ^ 3 + 666 * y ^ 2 - 36 * y + 1 := by
      rw [hrewrite_y]
      exact mul_nonneg (by positivity) (modifiedNarayanaTuran_nine_transformed_factor_nonneg v)
    have hrewrite_r :
        r ^ 16 + 36 * r ^ 15 + 666 * r ^ 14 + 6720 * r ^ 13 +
          41496 * r ^ 12 + 163800 * r ^ 11 + 428610 * r ^ 10 +
            757276 * r ^ 9 + 914706 * r ^ 8 + 757276 * r ^ 7 +
              428610 * r ^ 6 + 163800 * r ^ 5 + 41496 * r ^ 4 +
                6720 * r ^ 3 + 666 * r ^ 2 + 36 * r + 1 =
          y ^ 16 - 36 * y ^ 15 + 666 * y ^ 14 - 6720 * y ^ 13 +
            41496 * y ^ 12 - 163800 * y ^ 11 + 428610 * y ^ 10 -
              757276 * y ^ 9 + 914706 * y ^ 8 - 757276 * y ^ 7 +
                428610 * y ^ 6 - 163800 * y ^ 5 + 41496 * y ^ 4 -
                  6720 * y ^ 3 + 666 * y ^ 2 - 36 * y + 1 := by
      dsimp [y]
      ring
    rwa [hrewrite_r]

private theorem modifiedNarayanaTuran_ten_transformed_factor_nonneg
    {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ v ^ 9 - 27 * v ^ 8 + 450 * v ^ 7 - 2856 * v ^ 6 +
      11088 * v ^ 5 - 16632 * v ^ 4 + 19404 * v ^ 3 + 5292 * v + 1764 := by
  have hdecomp :
      v ^ 9 - 27 * v ^ 8 + 450 * v ^ 7 - 2856 * v ^ 6 +
        11088 * v ^ 5 - 16632 * v ^ 4 + 19404 * v ^ 3 + 5292 * v + 1764 =
        v * (-(6129 / 44) * v + (1358 / 19) * v ^ 2 -
          (927 / 50) * v ^ 3 + (37 / 50) * v ^ 4) ^ 2 +
        1764 + 5292 * v + (1503 / 1936) * v ^ 3 +
          (685503 / 209) * v ^ 4 + (323412937 / 397100) * v ^ 5 +
            (8391 / 20900) * v ^ 6 + (23149 / 47500) * v ^ 7 +
              (549 / 1250) * v ^ 8 + (1131 / 2500) * v ^ 9 := by
    ring
  rw [hdecomp]
  positivity

private theorem modifiedNarayanaTuran_ten_factor_nonneg_of_nonpos
    {r : ℝ} (hr : r ≤ 0) :
    0 ≤ r ^ 18 + 45 * r ^ 17 + 1035 * r ^ 16 + 13212 * r ^ 15 +
      104490 * r ^ 14 + 537516 * r ^ 13 + 1866690 * r ^ 12 +
        4475340 * r ^ 11 + 7522164 * r ^ 10 + 8934770 * r ^ 9 +
          7522164 * r ^ 8 + 4475340 * r ^ 7 + 1866690 * r ^ 6 +
            537516 * r ^ 5 + 104490 * r ^ 4 + 13212 * r ^ 3 +
              1035 * r ^ 2 + 45 * r + 1 := by
  let y : ℝ := -r
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    linarith
  by_cases hy_zero : y = 0
  · have hr_zero : r = 0 := by
      dsimp [y] at hy_zero
      linarith
    rw [hr_zero]
    norm_num
  · have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy_zero)
    let v : ℝ := (y - 1) ^ 2 / y
    have hv_nonneg : 0 ≤ v := by
      dsimp [v]
      exact div_nonneg (sq_nonneg (y - 1)) hy_nonneg
    have hrewrite_y :
        y ^ 18 - 45 * y ^ 17 + 1035 * y ^ 16 - 13212 * y ^ 15 +
          104490 * y ^ 14 - 537516 * y ^ 13 + 1866690 * y ^ 12 -
            4475340 * y ^ 11 + 7522164 * y ^ 10 - 8934770 * y ^ 9 +
              7522164 * y ^ 8 - 4475340 * y ^ 7 + 1866690 * y ^ 6 -
                537516 * y ^ 5 + 104490 * y ^ 4 - 13212 * y ^ 3 +
                  1035 * y ^ 2 - 45 * y + 1 =
          y ^ 9 * (v ^ 9 - 27 * v ^ 8 + 450 * v ^ 7 - 2856 * v ^ 6 +
            11088 * v ^ 5 - 16632 * v ^ 4 + 19404 * v ^ 3 + 5292 * v +
              1764) := by
      dsimp [v]
      field_simp [hy_pos.ne']
      ring
    have hnonneg_y :
        0 ≤ y ^ 18 - 45 * y ^ 17 + 1035 * y ^ 16 - 13212 * y ^ 15 +
          104490 * y ^ 14 - 537516 * y ^ 13 + 1866690 * y ^ 12 -
            4475340 * y ^ 11 + 7522164 * y ^ 10 - 8934770 * y ^ 9 +
              7522164 * y ^ 8 - 4475340 * y ^ 7 + 1866690 * y ^ 6 -
                537516 * y ^ 5 + 104490 * y ^ 4 - 13212 * y ^ 3 +
                  1035 * y ^ 2 - 45 * y + 1 := by
      rw [hrewrite_y]
      exact mul_nonneg (by positivity)
        (modifiedNarayanaTuran_ten_transformed_factor_nonneg hv_nonneg)
    have hrewrite_r :
        r ^ 18 + 45 * r ^ 17 + 1035 * r ^ 16 + 13212 * r ^ 15 +
          104490 * r ^ 14 + 537516 * r ^ 13 + 1866690 * r ^ 12 +
            4475340 * r ^ 11 + 7522164 * r ^ 10 + 8934770 * r ^ 9 +
              7522164 * r ^ 8 + 4475340 * r ^ 7 + 1866690 * r ^ 6 +
                537516 * r ^ 5 + 104490 * r ^ 4 + 13212 * r ^ 3 +
                  1035 * r ^ 2 + 45 * r + 1 =
          y ^ 18 - 45 * y ^ 17 + 1035 * y ^ 16 - 13212 * y ^ 15 +
            104490 * y ^ 14 - 537516 * y ^ 13 + 1866690 * y ^ 12 -
              4475340 * y ^ 11 + 7522164 * y ^ 10 - 8934770 * y ^ 9 +
                7522164 * y ^ 8 - 4475340 * y ^ 7 + 1866690 * y ^ 6 -
                  537516 * y ^ 5 + 104490 * y ^ 4 - 13212 * y ^ 3 +
                    1035 * y ^ 2 - 45 * y + 1 := by
      dsimp [y]
      ring
    rwa [hrewrite_r]

/-- The first three Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_three
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₃ : m ≤ 3) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)

/-- Bounded Turan package through `m = 3`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_three :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 3 := by
  intro m r hm₁ hm₃ hr
  exact modifiedNarayanaTuran_nonneg_of_le_three hm₁ hm₃ hr

/-- The first four Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_four
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₄ : m ≤ 4) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_four]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_four_factor_nonneg r)

/-- Bounded Turan package through `m = 4`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_four :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 4 := by
  intro m r hm₁ hm₄ hr
  exact modifiedNarayanaTuran_nonneg_of_le_four hm₁ hm₄ hr

/-- The first five Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_five
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₅ : m ≤ 5) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_four]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_four_factor_nonneg r)
  · rw [modifiedNarayanaTuran_five]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_five_factor_nonneg_of_nonpos hr)

/-- Bounded Turan package through `m = 5`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_five :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 5 := by
  intro m r hm₁ hm₅ hr
  exact modifiedNarayanaTuran_nonneg_of_le_five hm₁ hm₅ hr

/-- The first six Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_six
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₆ : m ≤ 6) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_four]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_four_factor_nonneg r)
  · rw [modifiedNarayanaTuran_five]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_five_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_six]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_six_factor_nonneg_of_nonpos hr)

/-- Bounded Turan package through `m = 6`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_six :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 6 := by
  intro m r hm₁ hm₆ hr
  exact modifiedNarayanaTuran_nonneg_of_le_six hm₁ hm₆ hr

/-- The first seven Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_seven
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₇ : m ≤ 7) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_four]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_four_factor_nonneg r)
  · rw [modifiedNarayanaTuran_five]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_five_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_six]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_six_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_seven]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_seven_factor_nonneg_of_nonpos hr)

/-- Bounded Turan package through `m = 7`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_seven :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 7 := by
  intro m r hm₁ hm₇ hr
  exact modifiedNarayanaTuran_nonneg_of_le_seven hm₁ hm₇ hr

/-- The first eight Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_eight
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₈ : m ≤ 8) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_four]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_four_factor_nonneg r)
  · rw [modifiedNarayanaTuran_five]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_five_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_six]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_six_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_seven]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_seven_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_eight]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_eight_factor_nonneg_of_nonpos hr)

/-- Bounded Turan package through `m = 8`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_eight :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 8 := by
  intro m r hm₁ hm₈ hr
  exact modifiedNarayanaTuran_nonneg_of_le_eight hm₁ hm₈ hr

/-- The first nine Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_nine
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₉ : m ≤ 9) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_four]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_four_factor_nonneg r)
  · rw [modifiedNarayanaTuran_five]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_five_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_six]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_six_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_seven]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_seven_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_eight]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_eight_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_nine]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_nine_factor_nonneg_of_nonpos hr)

/-- Bounded Turan package through `m = 9`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_nine :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 9 := by
  intro m r hm₁ hm₉ hr
  exact modifiedNarayanaTuran_nonneg_of_le_nine hm₁ hm₉ hr

/-- The first ten Narayana Turan inequalities on nonpositive inputs. -/
theorem modifiedNarayanaTuran_nonneg_of_le_ten
    {m : ℕ} {r : ℝ} (hm₁ : 1 ≤ m) (hm₁₀ : m ≤ 10) (hr : r ≤ 0) :
    0 ≤ modifiedNarayanaTuran m r := by
  interval_cases m
  · rw [modifiedNarayanaTuran_one]
    linarith
  · rw [modifiedNarayanaTuran_two]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_two_factor_nonneg r)
  · rw [modifiedNarayanaTuran_three]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_three_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_four]
    exact mul_nonneg (by linarith) (modifiedNarayanaTuran_four_factor_nonneg r)
  · rw [modifiedNarayanaTuran_five]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_five_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_six]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_six_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_seven]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_seven_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_eight]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_eight_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_nine]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_nine_factor_nonneg_of_nonpos hr)
  · rw [modifiedNarayanaTuran_ten]
    exact mul_nonneg (by linarith)
      (modifiedNarayanaTuran_ten_factor_nonneg_of_nonpos hr)

/-- Bounded Turan package through `m = 10`. -/
theorem modifiedNarayanaTuranNonnegOnNonpos_upTo_ten :
    ModifiedNarayanaTuranNonnegOnNonposUpToStatement 10 := by
  intro m r hm₁ hm₁₀ hr
  exact modifiedNarayanaTuran_nonneg_of_le_ten hm₁ hm₁₀ hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 3`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_three
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₃ : m ≤ 3)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₃ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_three hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 4`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_four
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₄ : m ≤ 4)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₄ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_four hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 5`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_five
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₅ : m ≤ 5)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₅ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_five hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 6`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_six
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₆ : m ≤ 6)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₆ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_six hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 7`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_seven
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₇ : m ≤ 7)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₇ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_seven hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 8`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_eight
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₈ : m ≤ 8)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₈ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_eight hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 9`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_nine
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₉ : m ≤ 9)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₉ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_nine hr

/-- Checked shifted Lemma 3.4 root-sign test through `m = 10`. -/
theorem lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_le_ten
    {m : ℕ} {lam mu r : ℝ} (hm : 1 ≤ m) (hm₁₀ : m ≤ 10)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hr : (((C lam * X + C mu) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C mu) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayanaShifted_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₁₀ hlam hmu modifiedNarayanaTuranNonnegOnNonpos_upTo_ten hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 3`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_three
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₃ : m ≤ 3)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₃ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_three hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 4`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_four
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₄ : m ≤ 4)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₄ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_four hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 5`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_five
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₅ : m ≤ 5)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₅ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_five hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 6`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_six
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₆ : m ≤ 6)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₆ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_six hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 7`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_seven
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₇ : m ≤ 7)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₇ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_seven hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 8`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_eight
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₈ : m ≤ 8)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₈ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_eight hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 9`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_nine
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₉ : m ≤ 9)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₉ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_nine hr

/-- Checked paper-shaped Lemma 3.4 root-sign test through `m = 10`. -/
theorem lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_le_ten
    {m : ℕ} {lam nu r : ℝ} (hm : 1 ≤ m) (hm₁₀ : m ≤ 10)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hr : (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).IsRoot r)) :
    (((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)).eval r) *
      (modifiedNarayanaPolynomial (m - 1)).eval r ≤ 0 :=
  lemma34ModifiedNarayana_right_eval_mul_prev_nonpos_of_turanNonnegUpTo
    hm hm₁₀ hlam hnu modifiedNarayanaTuranNonnegOnNonpos_upTo_ten hr

end GeneralizedSnakePosets
end RealRooted
