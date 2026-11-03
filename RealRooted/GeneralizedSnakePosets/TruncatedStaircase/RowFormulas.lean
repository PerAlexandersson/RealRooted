module

public import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.BottomRow

/-!
# General row formulas for truncated staircases

This module derives the bottom-row coefficient recurrence, closed formulas for
one through three rows, and the finite tail sums used in those inductions.
-/

@[expose] public section

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
            Nat.choose (n + 2) 2 + Nat.choose (n + 2) 3 :=
        Nat.choose_succ_succ (n + 2) 2
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

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
