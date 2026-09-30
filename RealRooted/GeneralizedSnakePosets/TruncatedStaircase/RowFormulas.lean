import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.BottomRow

/-!
# General row formulas for truncated staircases

This module derives the bottom-row coefficient recurrence, closed formulas for
one through six rows, and the finite tail sums used in those inductions.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

/-- Coefficients commute with finite list sums of polynomials. -/
private lemma listSum_coeff (ps : List ℝ[X]) (k : ℕ) :
    ps.sum.coeff k = (ps.map fun p => p.coeff k).sum := by
  induction ps with
  | nil =>
      simp
  | cons p ps ih =>
      simp [ih, Polynomial.coeff_add]

/-- Truncated-staircase rook polynomials are nonzero. -/
theorem truncatedStaircaseRookPolynomial_ne_zero (n i : ℕ) :
    truncatedStaircaseRookPolynomial n i ≠ 0 :=
  rookPolynomial_ne_zero _

/-- Bottom-row expansion for truncated-staircase rook polynomials: split
placements according to whether the last row is empty, and if not, according
to the column of its unique rook. -/
def truncatedStaircaseBottomRowExpansion (n i : ℕ) : Prop :=
  truncatedStaircaseRookPolynomial n (i + 1) =
    truncatedStaircaseRookPolynomial n i +
      X * ((List.range (n - i)).map fun c =>
        truncatedStaircaseRookPolynomial (n - c - 1) i).sum

/-- The bottom-row expansion holds for every truncated staircase. -/
theorem truncatedStaircaseBottomRowExpansion_all (n i : ℕ) :
    truncatedStaircaseBottomRowExpansion n i := by
  dsimp [truncatedStaircaseBottomRowExpansion]
  rw [truncatedStaircaseRookPolynomial, rookPolynomial_eq_nonNestingPlacements_sum]
  rw [sum_nonNestingPlacements_succ_eq_withoutBottomRow_add_bottomRow]
  rw [sum_nonNestingPlacementsWithoutBottomRow_eq_truncatedStaircaseRookPolynomial]
  rw [sum_bottomRowCells_nonNestingPlacementsWithCell_eq_mul_sum]

/-- The constant coefficient is unchanged by adding the bottom row. -/
theorem coeff_truncatedStaircaseRookPolynomial_succ_zero (n i : ℕ) :
    (truncatedStaircaseRookPolynomial n (i + 1)).coeff 0 =
      (truncatedStaircaseRookPolynomial n i).coeff 0 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n i
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [hbottom, Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, add_zero]

/-- Coefficient form of the bottom-row expansion for positive powers of `X`. -/
theorem coeff_truncatedStaircaseRookPolynomial_succ_succ (n i k : ℕ) :
    (truncatedStaircaseRookPolynomial n (i + 1)).coeff (k + 1) =
      (truncatedStaircaseRookPolynomial n i).coeff (k + 1) +
        ((List.range (n - i)).map fun c =>
          (truncatedStaircaseRookPolynomial (n - c - 1) i).coeff k).sum := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n i
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [hbottom, Polynomial.coeff_add, Polynomial.coeff_X_mul]
  rw [listSum_coeff, List.map_map]
  simp [Function.comp_def]

/-- The one-row truncated staircase with `n` cells has rook polynomial
`1 + nX`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_one_row (n : ℕ) :
    truncatedStaircaseRookPolynomial n 1 = 1 + C (n : ℝ) * X := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 0
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  simp only [truncatedStaircaseRookPolynomial_zero_rows] at hbottom
  rw [hbottom]
  induction n with
  | zero =>
      simp
  | succ n _ =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [Nat.cast_succ, add_comm, mul_add, add_mul]
      ring_nf

/-- Cast the quadratic binomial coefficient to the ambient real field. -/
private theorem nat_choose_two_cast_real (n : ℕ) :
    ((Nat.choose n 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
  Nat.cast_choose_two (K := ℝ) n

/-- Add two cubic polynomials written by coefficients. -/
private theorem add_cubic_coeffs (a b c d e f g : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 : ℝ[X]) +
      (C d + C e * X + C f * X ^ 2 + C g * X ^ 3) =
        C (1 + d) + C (a + e) * X + C (b + f) * X ^ 2 +
          C (c + g) * X ^ 3 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add]
  rw [Polynomial.C_1]
  ring_nf

/-- Add a cubic polynomial to `X` times another cubic polynomial. -/
private theorem add_X_mul_cubic_coeffs (a b c d e f g : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 : ℝ[X]) +
      X * (C d + C e * X + C f * X ^ 2 + C g * X ^ 3) =
        1 + C (a + d) * X + C (b + e) * X ^ 2 +
          C (c + f) * X ^ 3 + C g * X ^ 4 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add]
  ring_nf

/-- Add two quartic polynomials written by coefficients. -/
private theorem add_quartic_coeffs (a b c d e f g h i : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 : ℝ[X]) +
      (C e + C f * X + C g * X ^ 2 + C h * X ^ 3 + C i * X ^ 4) =
        C (1 + e) + C (a + f) * X + C (b + g) * X ^ 2 +
          C (c + h) * X ^ 3 + C (d + i) * X ^ 4 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add,
    Polynomial.C_add]
  rw [Polynomial.C_1]
  ring_nf

/-- Add a quartic polynomial to `X` times another quartic polynomial. -/
private theorem add_X_mul_quartic_coeffs (a b c d e f g h i : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 : ℝ[X]) +
      X * (C e + C f * X + C g * X ^ 2 + C h * X ^ 3 + C i * X ^ 4) =
        1 + C (a + e) * X + C (b + f) * X ^ 2 +
          C (c + g) * X ^ 3 + C (d + h) * X ^ 4 + C i * X ^ 5 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add]
  ring_nf

/-- Add two quintic polynomials written by coefficients. -/
private theorem add_quintic_coeffs (a b c d e f g h i j k : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 +
        C e * X ^ 5 : ℝ[X]) +
      (C f + C g * X + C h * X ^ 2 + C i * X ^ 3 + C j * X ^ 4 +
        C k * X ^ 5) =
        C (1 + f) + C (a + g) * X + C (b + h) * X ^ 2 +
          C (c + i) * X ^ 3 + C (d + j) * X ^ 4 + C (e + k) * X ^ 5 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add,
    Polynomial.C_add, Polynomial.C_add]
  rw [Polynomial.C_1]
  ring_nf

/-- Add a quintic polynomial to `X` times another quintic polynomial. -/
private theorem add_X_mul_quintic_coeffs (a b c d e f g h i j k : ℝ) :
    (1 + C a * X + C b * X ^ 2 + C c * X ^ 3 + C d * X ^ 4 +
        C e * X ^ 5 : ℝ[X]) +
      X * (C f + C g * X + C h * X ^ 2 + C i * X ^ 3 + C j * X ^ 4 +
        C k * X ^ 5) =
        1 + C (a + f) * X + C (b + g) * X ^ 2 +
          C (c + h) * X ^ 3 + C (d + i) * X ^ 4 + C (e + j) * X ^ 5 +
            C k * X ^ 6 := by
  rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_add, Polynomial.C_add,
    Polynomial.C_add]
  ring_nf

/-- The same tail sum with a direct row-count parameter. -/
private theorem truncatedStaircaseRookPolynomial_one_row_tail_sum_direct (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 1 - c - 1) 1).sum =
      C (n : ℝ) + C (Nat.choose (n + 1) 2 : ℝ) * X := by
  induction n with
  | zero =>
      simp [truncatedStaircaseRookPolynomial_one_row]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one, Nat.add_sub_add_right,
        Nat.add_sub_cancel_right, tsub_zero]
      change truncatedStaircaseRookPolynomial (n + 1) 1 +
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 - c - 1) 1).sum =
        C ((n + 1 : ℕ) : ℝ) + C (Nat.choose (n + 1 + 1) 2 : ℝ) * X
      rw [ih, truncatedStaircaseRookPolynomial_one_row]
      have hchoose :
          Nat.choose (n + 1 + 1) 2 = Nat.choose (n + 1) 2 + (n + 1) := by
        rw [show n + 1 + 1 = Nat.succ (n + 1) by rfl]
        rw [show 2 = Nat.succ 1 by rfl, Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
      rw [hchoose]
      simp [Nat.cast_add, Polynomial.C_add, add_comm, add_left_comm, add_assoc,
        add_mul]

/-- Tail sum of one-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_one_row_tail_sum (n : ℕ) :
    ((List.range (n - 1)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 1).sum =
      C ((n - 1 : ℕ) : ℝ) + C (Nat.choose n 2 : ℝ) * X := by
  by_cases hn : n = 0
  · subst n
    simp [truncatedStaircaseRookPolynomial_one_row]
  · have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
    simpa [hnsub] using
      truncatedStaircaseRookPolynomial_one_row_tail_sum_direct (n - 1)

/-- The two-row truncated staircase with row lengths `n` and `n - 1` has rook
polynomial `1 + (2n - 1)X + binom(n,2)X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_two_rows (n : ℕ) :
    truncatedStaircaseRookPolynomial n 2 =
      1 + C ((2 * n - 1 : ℕ) : ℝ) * X + C (Nat.choose n 2 : ℝ) * X ^ 2 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 1
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_one_row,
    truncatedStaircaseRookPolynomial_one_row_tail_sum n] at hbottom
  rw [hbottom]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn_pos]
      norm_num
    rw [hcast_sub]
    have hC2n : (C ((2 * n - 1 : ℕ) : ℝ) : ℝ[X]) = C ((2 : ℝ) * n - 1) := by
      rw [show ((2 * n - 1 : ℕ) : ℝ) = (2 : ℝ) * n - 1 by
        rw [Nat.cast_sub (by lia : 1 ≤ 2 * n)]
        norm_num]
    rw [hC2n]
    have hXcoeff :
        C (n : ℝ) + C ((n : ℝ) - 1) = (C ((2 : ℝ) * n - 1) : ℝ[X]) := by
      rw [← Polynomial.C_add]
      ring_nf
    calc
      1 + C (n : ℝ) * X + X * (C ((n : ℝ) - 1) +
            C (Nat.choose n 2 : ℝ) * X)
          = 1 + (C (n : ℝ) + C ((n : ℝ) - 1)) * X +
              C (Nat.choose n 2 : ℝ) * X ^ 2 := by
            ring_nf
      _ = 1 + C ((2 : ℝ) * n - 1) * X +
            C (Nat.choose n 2 : ℝ) * X ^ 2 := by rw [hXcoeff]

/-- Tail sum of two-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_two_rows_tail_sum_direct (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 2 - c - 1) 2).sum =
      C (n : ℝ) + C ((n * (n + 2) : ℕ) : ℝ) * X +
        C (Nat.choose (n + 2) 3 : ℝ) * X ^ 2 := by
  induction n with
  | zero =>
      simp [truncatedStaircaseRookPolynomial_two_rows]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 2 - 0 - 1 = n + 2 := by lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 2 - (c + 1) - 1) 2).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 2 - c - 1) 2).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih, truncatedStaircaseRookPolynomial_two_rows]
      have hchoose :
          Nat.choose (n + 1 + 2) 3 =
            Nat.choose (n + 2) 2 + Nat.choose (n + 2) 3 := by
        calc
          Nat.choose (n + 1 + 2) 3 =
              Nat.choose (Nat.succ (n + 2)) 3 := by rfl
          _ = Nat.choose (n + 2) 2 + Nat.choose (n + 2) 3 :=
              by simpa using Nat.choose_succ_succ (n + 2) 2
      have hchoose2 :
          Nat.choose (n + 2) 2 = (n + 1) + Nat.choose (n + 1) 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ (n + 1) 1
      rw [hchoose, hchoose2]
      have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
      simp only [Order.lt_two_iff, zero_le, mul_pos_iff_of_pos_left, add_pos_iff,
        or_true, Nat.cast_pred, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
        map_sub, map_mul, map_add, map_natCast, map_one, Nat.cast_one]
      rw [hC2]
      ring_nf

/-- Tail sum of two-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_two_rows_tail_sum (n : ℕ)
    (hn : 2 ≤ n) :
    ((List.range (n - 2)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 2).sum =
      C ((n - 2 : ℕ) : ℝ) + C (((n - 2) * n : ℕ) : ℝ) * X +
        C (Nat.choose n 3 : ℝ) * X ^ 2 := by
  have hnsub : n - 2 + 2 = n := Nat.sub_add_cancel hn
  simpa [hnsub] using
    truncatedStaircaseRookPolynomial_two_rows_tail_sum_direct (n - 2)

/-- The three-row truncated staircase with row lengths `n`, `n - 1`, and
`n - 2` has rook polynomial
`1 + 3(n - 1)X + (binom(n,2) + n(n - 2))X^2 + binom(n,3)X^3`. -/
theorem truncatedStaircaseRookPolynomial_three_rows (n : ℕ) (hn : 3 ≤ n) :
    truncatedStaircaseRookPolynomial n 3 =
      1 + C ((3 * n - 3 : ℕ) : ℝ) * X +
        C ((Nat.choose n 2 + (n - 2) * n : ℕ) : ℝ) * X ^ 2 +
          C (Nat.choose n 3 : ℝ) * X ^ 3 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 2
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_two_rows,
    truncatedStaircaseRookPolynomial_two_rows_tail_sum n (by lia : 2 ≤ n)] at hbottom
  rw [hbottom]
  have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 3) hn
  have hn_two : 2 ≤ n := by lia
  have hcast_sub_two : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn_two]
    norm_num
  rw [hcast_sub_two]
  have hC2n :
      (C ((2 * n - 1 : ℕ) : ℝ) : ℝ[X]) = C ((2 : ℝ) * n - 1) := by
    rw [show ((2 * n - 1 : ℕ) : ℝ) = (2 : ℝ) * n - 1 by
      rw [Nat.cast_sub (by lia : 1 ≤ 2 * n)]
      norm_num]
  have hCtail :
      (C (((n - 2) * n : ℕ) : ℝ) : ℝ[X]) = C (((n : ℝ) - 2) * n) := by
    rw [Nat.cast_mul, hcast_sub_two]
  have hC3n :
      (C ((3 * n - 3 : ℕ) : ℝ) : ℝ[X]) = C ((3 : ℝ) * n - 3) := by
    rw [show ((3 * n - 3 : ℕ) : ℝ) = (3 : ℝ) * n - 3 by
      rw [Nat.cast_sub (by lia : 3 ≤ 3 * n)]
      norm_num]
  have hCtwo :
      (C ((Nat.choose n 2 + (n - 2) * n : ℕ) : ℝ) : ℝ[X]) =
        C ((Nat.choose n 2 : ℝ) + ((n : ℝ) - 2) * n) := by
    rw [Nat.cast_add, Nat.cast_mul, hcast_sub_two]
  rw [hC2n, hCtail, hC3n, hCtwo]
  have hXcoeff :
      C ((2 : ℝ) * n - 1) + C ((n : ℝ) - 2) =
        (C ((3 : ℝ) * n - 3) : ℝ[X]) := by
    rw [← Polynomial.C_add]
    ring_nf
  calc
    1 + C ((2 : ℝ) * n - 1) * X + C (Nat.choose n 2 : ℝ) * X ^ 2 +
        X * (C ((n : ℝ) - 2) + C (((n : ℝ) - 2) * n) * X +
          C (Nat.choose n 3 : ℝ) * X ^ 2)
        = 1 + (C ((2 : ℝ) * n - 1) + C ((n : ℝ) - 2)) * X +
          (C (Nat.choose n 2 : ℝ) + C (((n : ℝ) - 2) * n)) * X ^ 2 +
            C (Nat.choose n 3 : ℝ) * X ^ 3 := by
          ring_nf
    _ = 1 + C ((3 : ℝ) * n - 3) * X +
        C ((Nat.choose n 2 : ℝ) + ((n : ℝ) - 2) * n) * X ^ 2 +
          C (Nat.choose n 3 : ℝ) * X ^ 3 := by
        rw [hXcoeff, ← Polynomial.C_add]

/-- Tail sum of three-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_three_rows_tail_sum_direct
    (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 3 - c - 1) 3).sum =
      C (n : ℝ) +
        C ((3 : ℝ) * (Nat.choose (n + 2) 2 : ℝ) - 3) * X +
          C ((3 : ℝ) * (Nat.choose (n + 3) 3 : ℝ) -
            (Nat.choose (n + 3) 2 : ℝ)) * X ^ 2 +
            C (Nat.choose (n + 3) 4 : ℝ) * X ^ 3 := by
  induction n with
  | zero =>
      norm_num [Nat.choose]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 3 - 0 - 1 = n + 3 := by lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 3 - (c + 1) - 1) 3).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 3 - c - 1) 3).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih,
        truncatedStaircaseRookPolynomial_three_rows (n + 3) (by lia)]
      have hCheadX :
          (C ((3 * (n + 3) - 3 : ℕ) : ℝ) : ℝ[X]) =
            C ((3 : ℝ) * (n + 3) - 3) := by
        rw [show ((3 * (n + 3) - 3 : ℕ) : ℝ) =
            (3 : ℝ) * (n + 3) - 3 by
          rw [Nat.cast_sub (by lia : 3 ≤ 3 * (n + 3))]
          norm_num]
      have hCheadX2 :
          (C ((Nat.choose (n + 3) 2 + (n + 3 - 2) * (n + 3) : ℕ) : ℝ) :
              ℝ[X]) =
            C ((Nat.choose (n + 3) 2 : ℝ) + ((n : ℝ) + 1) * ((n : ℝ) + 3)) := by
        have hsub : ((n + 3 - 2 : ℕ) : ℝ) = (n : ℝ) + 1 := by
          rw [Nat.cast_sub (by lia : 2 ≤ n + 3)]
          norm_num
          ring_nf
        rw [show ((Nat.choose (n + 3) 2 + (n + 3 - 2) * (n + 3) : ℕ) : ℝ) =
            (Nat.choose (n + 3) 2 : ℝ) +
              ((n : ℝ) + 1) * ((n : ℝ) + 3) by
          rw [Nat.cast_add, Nat.cast_mul, hsub]
          norm_num
          ]
      have hchoose3 :
          Nat.choose (n + 1 + 3) 3 =
            Nat.choose (n + 3) 2 + Nat.choose (n + 3) 3 := by
        calc
          Nat.choose (n + 1 + 3) 3 =
              Nat.choose (Nat.succ (n + 3)) 3 := by rfl
          _ = Nat.choose (n + 3) 2 + Nat.choose (n + 3) 3 :=
              by simpa using Nat.choose_succ_succ (n + 3) 2
      have hchoose2 :
          Nat.choose (n + 1 + 3) 2 =
            Nat.choose (n + 3) 1 + Nat.choose (n + 3) 2 := by
        calc
          Nat.choose (n + 1 + 3) 2 =
              Nat.choose (Nat.succ (n + 3)) 2 := by rfl
          _ = Nat.choose (n + 3) 1 + Nat.choose (n + 3) 2 :=
              by simpa using Nat.choose_succ_succ (n + 3) 1
      have hchoose4 :
          Nat.choose (n + 1 + 3) 4 =
            Nat.choose (n + 3) 3 + Nat.choose (n + 3) 4 := by
        calc
          Nat.choose (n + 1 + 3) 4 =
              Nat.choose (Nat.succ (n + 3)) 4 := by rfl
          _ = Nat.choose (n + 3) 3 + Nat.choose (n + 3) 4 :=
              by simpa using Nat.choose_succ_succ (n + 3) 3
      have hchoose2_prev :
          ((Nat.choose (n + 2) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
        have h := nat_choose_two_cast_real (n + 2)
        norm_num at h
        linarith
      have hchoose2_head :
          ((Nat.choose (n + 3) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 3) * ((n : ℝ) + 2) / 2 := by
        have h := nat_choose_two_cast_real (n + 3)
        norm_num at h
        linarith
      rw [hCheadX, hCheadX2, hchoose3, hchoose2, hchoose4]
      rw [add_cubic_coeffs]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [hchoose2_prev, hchoose2_head]
      congr 1
      all_goals ring_nf

/-- Tail sum of three-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_three_rows_tail_sum (n : ℕ)
    (hn : 3 ≤ n) :
    ((List.range (n - 3)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 3).sum =
      C ((n - 3 : ℕ) : ℝ) +
        C ((3 : ℝ) * (Nat.choose (n - 1) 2 : ℝ) - 3) * X +
          C ((3 : ℝ) * (Nat.choose n 3 : ℝ) -
            (Nat.choose n 2 : ℝ)) * X ^ 2 +
            C (Nat.choose n 4 : ℝ) * X ^ 3 := by
  have hnsub_three : n - 3 + 3 = n := Nat.sub_add_cancel hn
  have hnsub_two : n - 3 + 2 = n - 1 := by lia
  simpa [hnsub_three, hnsub_two] using
    truncatedStaircaseRookPolynomial_three_rows_tail_sum_direct (n - 3)

/-- The four-row truncated staircase with row lengths `n`, `n - 1`, `n - 2`,
and `n - 3` has rook polynomial
`1 + (4n - 6)X + n(3n - 7)X^2 +
(4 binom(n,3) - binom(n,2))X^3 + binom(n,4)X^4`. -/
theorem truncatedStaircaseRookPolynomial_four_rows (n : ℕ) (hn : 4 ≤ n) :
    truncatedStaircaseRookPolynomial n 4 =
      1 + C ((4 : ℝ) * n - 6) * X +
        C ((n : ℝ) * ((3 : ℝ) * n - 7)) * X ^ 2 +
          C ((4 : ℝ) * (Nat.choose n 3 : ℝ) -
            (Nat.choose n 2 : ℝ)) * X ^ 3 +
            C (Nat.choose n 4 : ℝ) * X ^ 4 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 3
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_three_rows n (by lia),
    truncatedStaircaseRookPolynomial_three_rows_tail_sum n (by lia)] at hbottom
  rw [hbottom]
  have hn_three : 3 ≤ n := by lia
  have hn_two : 2 ≤ n := by lia
  have hcast_sub_three : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub hn_three]
    norm_num
  have hcast_sub_two : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn_two]
    norm_num
  rw [hcast_sub_three]
  have hC3n :
      (C ((3 * n - 3 : ℕ) : ℝ) : ℝ[X]) = C ((3 : ℝ) * n - 3) := by
    rw [show ((3 * n - 3 : ℕ) : ℝ) = (3 : ℝ) * n - 3 by
      rw [Nat.cast_sub (by lia : 3 ≤ 3 * n)]
      norm_num]
  have hCthree :
      (C ((Nat.choose n 2 + (n - 2) * n : ℕ) : ℝ) : ℝ[X]) =
        C ((Nat.choose n 2 : ℝ) + ((n : ℝ) - 2) * n) := by
    rw [Nat.cast_add, Nat.cast_mul, hcast_sub_two]
  rw [hC3n, hCthree]
  have hchoose2_n : ((Nat.choose n 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    nat_choose_two_cast_real n
  have hchoose2_tail :
      ((Nat.choose (n - 1) 2 : ℕ) : ℝ) =
        ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 := by
    rw [nat_choose_two_cast_real]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia : 1 ≤ n)]
      norm_num
    rw [hcast]
    ring_nf
  rw [add_X_mul_cubic_coeffs, hchoose2_n, hchoose2_tail]
  congr 1
  all_goals ring_nf

/-- Tail sum of four-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_four_rows_tail_sum_direct
    (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 4 - c - 1) 4).sum =
      C (n : ℝ) + C ((2 : ℝ) * n * ((n : ℝ) + 4)) * X +
        C ((6 : ℝ) * (Nat.choose (n + 4) 3 : ℝ) -
          (4 : ℝ) * (Nat.choose (n + 4) 2 : ℝ)) * X ^ 2 +
        C ((4 : ℝ) * (Nat.choose (n + 4) 4 : ℝ) -
          (Nat.choose (n + 4) 3 : ℝ)) * X ^ 3 +
        C (Nat.choose (n + 4) 5 : ℝ) * X ^ 4 := by
  induction n with
  | zero =>
      norm_num [Nat.choose]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 4 - 0 - 1 = n + 4 := by lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 4 - (c + 1) - 1) 4).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 4 - c - 1) 4).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih,
        truncatedStaircaseRookPolynomial_four_rows (n + 4) (by lia)]
      have hchoose2_succ :
          Nat.choose (n + 1 + 4) 2 =
            Nat.choose (n + 4) 1 + Nat.choose (n + 4) 2 := by
        calc
          Nat.choose (n + 1 + 4) 2 =
              Nat.choose (Nat.succ (n + 4)) 2 := by rfl
          _ = Nat.choose (n + 4) 1 + Nat.choose (n + 4) 2 :=
              by simpa using Nat.choose_succ_succ (n + 4) 1
      have hchoose3_succ :
          Nat.choose (n + 1 + 4) 3 =
            Nat.choose (n + 4) 2 + Nat.choose (n + 4) 3 := by
        calc
          Nat.choose (n + 1 + 4) 3 =
              Nat.choose (Nat.succ (n + 4)) 3 := by rfl
          _ = Nat.choose (n + 4) 2 + Nat.choose (n + 4) 3 :=
              by simpa using Nat.choose_succ_succ (n + 4) 2
      have hchoose4_succ :
          Nat.choose (n + 1 + 4) 4 =
            Nat.choose (n + 4) 3 + Nat.choose (n + 4) 4 := by
        calc
          Nat.choose (n + 1 + 4) 4 =
              Nat.choose (Nat.succ (n + 4)) 4 := by rfl
          _ = Nat.choose (n + 4) 3 + Nat.choose (n + 4) 4 :=
              by simpa using Nat.choose_succ_succ (n + 4) 3
      have hchoose5_succ :
          Nat.choose (n + 1 + 4) 5 =
            Nat.choose (n + 4) 4 + Nat.choose (n + 4) 5 := by
        calc
          Nat.choose (n + 1 + 4) 5 =
              Nat.choose (Nat.succ (n + 4)) 5 := by rfl
          _ = Nat.choose (n + 4) 4 + Nat.choose (n + 4) 5 :=
              by simpa using Nat.choose_succ_succ (n + 4) 4
      have hchoose2_head :
          ((Nat.choose (n + 4) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 4) * ((n : ℝ) + 3) / 2 := by
        have h := nat_choose_two_cast_real (n + 4)
        norm_num at h
        linarith
      rw [add_quartic_coeffs, hchoose2_succ, hchoose3_succ, hchoose4_succ,
        hchoose5_succ]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [hchoose2_head]
      congr 1
      all_goals ring_nf

/-- Tail sum of four-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_four_rows_tail_sum (n : ℕ)
    (hn : 4 ≤ n) :
    ((List.range (n - 4)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 4).sum =
      C ((n - 4 : ℕ) : ℝ) +
        C ((2 : ℝ) * ((n - 4 : ℕ) : ℝ) * (((n - 4 : ℕ) : ℝ) + 4)) * X +
        C ((6 : ℝ) * (Nat.choose n 3 : ℝ) -
          (4 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 2 +
        C ((4 : ℝ) * (Nat.choose n 4 : ℝ) -
          (Nat.choose n 3 : ℝ)) * X ^ 3 +
        C (Nat.choose n 5 : ℝ) * X ^ 4 := by
  have hnsub_four : n - 4 + 4 = n := Nat.sub_add_cancel hn
  simpa [hnsub_four] using
    truncatedStaircaseRookPolynomial_four_rows_tail_sum_direct (n - 4)

/-- The five-row truncated staircase with row lengths `n`, `n - 1`, `n - 2`,
`n - 3`, and `n - 4` has rook polynomial
`1 + (5n - 10)X + 5n(n - 3)X^2
+ (10 binom(n,3) - 5 binom(n,2))X^3
+ (5 binom(n,4) - binom(n,3))X^4 + binom(n,5)X^5`. -/
theorem truncatedStaircaseRookPolynomial_five_rows (n : ℕ) (hn : 5 ≤ n) :
    truncatedStaircaseRookPolynomial n 5 =
      1 + C ((5 : ℝ) * n - 10) * X +
        C ((5 : ℝ) * n * ((n : ℝ) - 3)) * X ^ 2 +
        C ((10 : ℝ) * (Nat.choose n 3 : ℝ) -
          (5 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 3 +
        C ((5 : ℝ) * (Nat.choose n 4 : ℝ) -
          (Nat.choose n 3 : ℝ)) * X ^ 4 +
        C (Nat.choose n 5 : ℝ) * X ^ 5 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 4
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_four_rows n (by lia),
    truncatedStaircaseRookPolynomial_four_rows_tail_sum n (by lia)] at hbottom
  rw [hbottom]
  have hcast_sub_four : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    rw [Nat.cast_sub (by lia : 4 ≤ n)]
    norm_num
  rw [hcast_sub_four]
  have hchoose2_n : ((Nat.choose n 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    nat_choose_two_cast_real n
  rw [add_X_mul_quartic_coeffs, hchoose2_n]
  congr 1
  all_goals ring_nf

/-- Tail sum of five-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_five_rows_tail_sum_direct
    (n : ℕ) :
    ((List.range n).map fun c =>
      truncatedStaircaseRookPolynomial (n + 5 - c - 1) 5).sum =
      C (n : ℝ) + C ((5 : ℝ) * n * ((n : ℝ) + 5) / 2) * X +
        C ((10 : ℝ) * (Nat.choose (n + 5) 3 : ℝ) -
          (10 : ℝ) * (Nat.choose (n + 5) 2 : ℝ)) * X ^ 2 +
        C ((10 : ℝ) * (Nat.choose (n + 5) 4 : ℝ) -
          (5 : ℝ) * (Nat.choose (n + 5) 3 : ℝ)) * X ^ 3 +
        C ((5 : ℝ) * (Nat.choose (n + 5) 5 : ℝ) -
          (Nat.choose (n + 5) 4 : ℝ)) * X ^ 4 +
        C (Nat.choose (n + 5) 6 : ℝ) * X ^ 5 := by
  induction n with
  | zero =>
      norm_num [Nat.choose]
  | succ n ih =>
      rw [List.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      have hhead : n + 1 + 5 - 0 - 1 = n + 5 := by lia
      have htail :
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 1 + 5 - (c + 1) - 1) 5).sum =
          ((List.range n).map fun c =>
            truncatedStaircaseRookPolynomial (n + 5 - c - 1) 5).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        have hc_lt : c < n := List.mem_range.mp hc
        congr 1
        lia
      rw [hhead, htail, ih,
        truncatedStaircaseRookPolynomial_five_rows (n + 5) (by lia)]
      have hchoose2_succ :
          Nat.choose (n + 1 + 5) 2 =
            Nat.choose (n + 5) 1 + Nat.choose (n + 5) 2 := by
        calc
          Nat.choose (n + 1 + 5) 2 =
              Nat.choose (Nat.succ (n + 5)) 2 := by rfl
          _ = Nat.choose (n + 5) 1 + Nat.choose (n + 5) 2 :=
              by simpa using Nat.choose_succ_succ (n + 5) 1
      have hchoose3_succ :
          Nat.choose (n + 1 + 5) 3 =
            Nat.choose (n + 5) 2 + Nat.choose (n + 5) 3 := by
        calc
          Nat.choose (n + 1 + 5) 3 =
              Nat.choose (Nat.succ (n + 5)) 3 := by rfl
          _ = Nat.choose (n + 5) 2 + Nat.choose (n + 5) 3 :=
              by simpa using Nat.choose_succ_succ (n + 5) 2
      have hchoose4_succ :
          Nat.choose (n + 1 + 5) 4 =
            Nat.choose (n + 5) 3 + Nat.choose (n + 5) 4 := by
        calc
          Nat.choose (n + 1 + 5) 4 =
              Nat.choose (Nat.succ (n + 5)) 4 := by rfl
          _ = Nat.choose (n + 5) 3 + Nat.choose (n + 5) 4 :=
              by simpa using Nat.choose_succ_succ (n + 5) 3
      have hchoose5_succ :
          Nat.choose (n + 1 + 5) 5 =
            Nat.choose (n + 5) 4 + Nat.choose (n + 5) 5 := by
        calc
          Nat.choose (n + 1 + 5) 5 =
              Nat.choose (Nat.succ (n + 5)) 5 := by rfl
          _ = Nat.choose (n + 5) 4 + Nat.choose (n + 5) 5 :=
              by simpa using Nat.choose_succ_succ (n + 5) 4
      have hchoose6_succ :
          Nat.choose (n + 1 + 5) 6 =
            Nat.choose (n + 5) 5 + Nat.choose (n + 5) 6 := by
        calc
          Nat.choose (n + 1 + 5) 6 =
              Nat.choose (Nat.succ (n + 5)) 6 := by rfl
          _ = Nat.choose (n + 5) 5 + Nat.choose (n + 5) 6 :=
              by simpa using Nat.choose_succ_succ (n + 5) 5
      have hchoose2_head :
          ((Nat.choose (n + 5) 2 : ℕ) : ℝ) =
            ((n : ℝ) + 5) * ((n : ℝ) + 4) / 2 := by
        have h := nat_choose_two_cast_real (n + 5)
        norm_num at h
        linarith
      rw [add_quintic_coeffs, hchoose2_succ, hchoose3_succ, hchoose4_succ,
        hchoose5_succ, hchoose6_succ]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      rw [hchoose2_head]
      congr 1
      all_goals ring_nf

/-- Tail sum of five-row truncated-staircase rook polynomials. -/
private theorem truncatedStaircaseRookPolynomial_five_rows_tail_sum (n : ℕ)
    (hn : 5 ≤ n) :
    ((List.range (n - 5)).map fun c =>
      truncatedStaircaseRookPolynomial (n - c - 1) 5).sum =
      C ((n - 5 : ℕ) : ℝ) +
        C ((5 : ℝ) * ((n - 5 : ℕ) : ℝ) *
          (((n - 5 : ℕ) : ℝ) + 5) / 2) * X +
        C ((10 : ℝ) * (Nat.choose n 3 : ℝ) -
          (10 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 2 +
        C ((10 : ℝ) * (Nat.choose n 4 : ℝ) -
          (5 : ℝ) * (Nat.choose n 3 : ℝ)) * X ^ 3 +
        C ((5 : ℝ) * (Nat.choose n 5 : ℝ) -
          (Nat.choose n 4 : ℝ)) * X ^ 4 +
        C (Nat.choose n 6 : ℝ) * X ^ 5 := by
  have hnsub_five : n - 5 + 5 = n := Nat.sub_add_cancel hn
  simpa [hnsub_five] using
    truncatedStaircaseRookPolynomial_five_rows_tail_sum_direct (n - 5)

/-- The six-row truncated staircase with row lengths `n`, `n - 1`, `n - 2`,
`n - 3`, `n - 4`, and `n - 5` has rook polynomial
`1 + (6n - 15)X + (5n(3n - 11)/2)X^2
+ (20 binom(n,3) - 15 binom(n,2))X^3
+ (15 binom(n,4) - 6 binom(n,3))X^4
+ (6 binom(n,5) - binom(n,4))X^5 + binom(n,6)X^6`. -/
theorem truncatedStaircaseRookPolynomial_six_rows (n : ℕ) (hn : 6 ≤ n) :
    truncatedStaircaseRookPolynomial n 6 =
      1 + C ((6 : ℝ) * n - 15) * X +
        C ((5 : ℝ) * n * ((3 : ℝ) * n - 11) / 2) * X ^ 2 +
        C ((20 : ℝ) * (Nat.choose n 3 : ℝ) -
          (15 : ℝ) * (Nat.choose n 2 : ℝ)) * X ^ 3 +
        C ((15 : ℝ) * (Nat.choose n 4 : ℝ) -
          (6 : ℝ) * (Nat.choose n 3 : ℝ)) * X ^ 4 +
        C ((6 : ℝ) * (Nat.choose n 5 : ℝ) -
          (Nat.choose n 4 : ℝ)) * X ^ 5 +
        C (Nat.choose n 6 : ℝ) * X ^ 6 := by
  have hbottom := truncatedStaircaseBottomRowExpansion_all n 5
  dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
  rw [truncatedStaircaseRookPolynomial_five_rows n (by lia),
    truncatedStaircaseRookPolynomial_five_rows_tail_sum n (by lia)] at hbottom
  rw [hbottom]
  have hcast_sub_five : ((n - 5 : ℕ) : ℝ) = (n : ℝ) - 5 := by
    rw [Nat.cast_sub (by lia : 5 ≤ n)]
    norm_num
  rw [hcast_sub_five]
  rw [add_X_mul_quintic_coeffs]
  congr 1
  all_goals ring_nf

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
