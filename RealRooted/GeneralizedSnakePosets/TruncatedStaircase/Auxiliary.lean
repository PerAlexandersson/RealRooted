import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.FiniteCases
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.RowFormulas

/-!
# Auxiliary polynomials from truncated staircases

This module assembles the truncated-staircase row polynomials into the
auxiliary family `G`, including the low-rank certificates and coefficient
nonnegativity interface used by the Braun--Jal development.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

/-- A finite list sum of nonnegative-coefficient polynomials has nonnegative
coefficients. -/
private lemma listSum_hasNonnegCoeffs {ps : List ℝ[X]}
    (hps : ∀ p ∈ ps, HasNonnegCoeffs p) :
    HasNonnegCoeffs ps.sum := by
  induction ps with
  | nil =>
      simp [HasNonnegCoeffs]
  | cons p ps ih =>
      intro k
      have hp : HasNonnegCoeffs p := hps p (by simp)
      have htail : ∀ q ∈ ps, HasNonnegCoeffs q := by
        intro q hq
        exact hps q (by simp [hq])
      simpa using add_nonneg (hp k) (ih htail k)

/-- The auxiliary polynomial `G_n` as a finite sum over truncated staircase
rook polynomials. -/
def auxiliaryG : ℕ → ℝ[X] :=
  fun n => ((List.range n).map fun i => truncatedStaircaseRookPolynomial n i).sum

/-- The finite-board auxiliary polynomial `G_0` is zero. -/
@[simp] theorem auxiliaryG_zero :
    auxiliaryG 0 = 0 := by
  simp [auxiliaryG]

/-- The finite-board auxiliary polynomial `G_1` is one. -/
@[simp] theorem auxiliaryG_one :
    auxiliaryG 1 = 1 := by
  simp [auxiliaryG]

/-- The finite-board auxiliary polynomial `G_2` is `2 + 2X`. -/
@[simp] theorem auxiliaryG_two :
    auxiliaryG 2 = 2 + C (2 : ℝ) * X := by
  rw [auxiliaryG, show List.range 2 = [0, 1] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_two_one]
  ring_nf

/-- The finite-board auxiliary polynomial `G_3` is `3 + 8X + 3X^2`. -/
@[simp] theorem auxiliaryG_three :
    auxiliaryG 3 = 3 + C (8 : ℝ) * X + C (3 : ℝ) * X ^ 2 := by
  rw [auxiliaryG, show List.range 3 = [0, 1, 2] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_three_one,
    truncatedStaircaseRookPolynomial_three_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC8 : (C (8 : ℝ) : ℝ[X]) = 8 := Polynomial.C_eq_natCast (R := ℝ) 8
  rw [hC3, hC5, hC8]
  ring_nf

/-- The expected `G_4` finite-board value follows from the remaining two-row
and three-row truncated-staircase computations. -/
theorem auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_two_three
    (h42 : truncatedStaircaseRookPolynomial 4 2 =
      1 + C (7 : ℝ) * X + C (6 : ℝ) * X ^ 2)
    (h43 : truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 := by
  rw [auxiliaryG, show List.range 4 = [0, 1, 2, 3] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_four_one, h42, h43]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 := Polynomial.C_eq_natCast (R := ℝ) 14
  have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 := Polynomial.C_eq_natCast (R := ℝ) 20
  rw [hC4, hC6, hC7, hC9, hC14, hC20]
  ring_nf

/-- The expected `G_4` finite-board value now follows from the remaining
three-row truncated-staircase computation. -/
theorem auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_three
    (h43 : truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 :=
  auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_two_three
    truncatedStaircaseRookPolynomial_four_two h43

/-- The finite-board auxiliary polynomial `G_4` is `4 + 20X + 20X^2 + 4X^3`. -/
@[simp] theorem auxiliaryG_four :
    auxiliaryG 4 = 4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
      C (4 : ℝ) * X ^ 3 :=
  auxiliaryG_four_of_truncatedStaircaseRookPolynomial_four_three
    truncatedStaircaseRookPolynomial_four_three

/-- The expected `G_5` finite-board value follows from the remaining
three-row and four-row truncated-staircase computations. -/
theorem auxiliaryG_five_of_truncatedStaircaseRookPolynomial_five_three_four
    (h53 : truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (h54 : truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4) :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 := by
  rw [auxiliaryG, show List.range 5 = [0, 1, 2, 3, 4] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_five_one,
    truncatedStaircaseRookPolynomial_five_two, h53, h54]
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
    Polynomial.C_eq_natCast (R := ℝ) 10
  have hC12 : (C (12 : ℝ) : ℝ[X]) = 12 :=
    Polynomial.C_eq_natCast (R := ℝ) 12
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 :=
    Polynomial.C_eq_natCast (R := ℝ) 14
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  have hC30 : (C (30 : ℝ) : ℝ[X]) = 30 :=
    Polynomial.C_eq_natCast (R := ℝ) 30
  have hC40 : (C (40 : ℝ) : ℝ[X]) = 40 :=
    Polynomial.C_eq_natCast (R := ℝ) 40
  have hC75 : (C (75 : ℝ) : ℝ[X]) = 75 :=
    Polynomial.C_eq_natCast (R := ℝ) 75
  rw [hC5, hC9, hC10, hC12, hC14, hC25, hC30, hC40, hC75]
  ring_nf

/-- The expected three-row `n = 5` truncated-staircase computation follows
from the bottom-row expansion into two-row truncated staircases. -/
theorem truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion
    (hbottom : truncatedStaircaseRookPolynomial 5 3 =
      truncatedStaircaseRookPolynomial 5 2 +
        X * (truncatedStaircaseRookPolynomial 4 2 +
          truncatedStaircaseRookPolynomial 3 2 +
            truncatedStaircaseRookPolynomial 2 2)) :
    truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3 := by
  rw [hbottom, truncatedStaircaseRookPolynomial_five_two,
    truncatedStaircaseRookPolynomial_four_two,
    truncatedStaircaseRookPolynomial_three_two,
    truncatedStaircaseRookPolynomial_two_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
    Polynomial.C_eq_natCast (R := ℝ) 10
  have hC12 : (C (12 : ℝ) : ℝ[X]) = 12 :=
    Polynomial.C_eq_natCast (R := ℝ) 12
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  rw [hC3, hC5, hC6, hC7, hC9, hC10, hC12, hC25]
  ring_nf

/-- The bottom-row expansion holds for the three-row staircase with row
lengths three, two, and one. -/
theorem truncatedStaircaseBottomRowExpansion_three_two :
    truncatedStaircaseBottomRowExpansion 3 2 := by
  dsimp [truncatedStaircaseBottomRowExpansion]
  simp only [add_zero]
  rw [truncatedStaircaseRookPolynomial_three_three,
    truncatedStaircaseRookPolynomial_three_two,
    truncatedStaircaseRookPolynomial_two_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  rw [hC3, hC5, hC6]
  ring_nf

/-- The bottom-row expansion holds for the three-row staircase with row
lengths four, three, and two. -/
theorem truncatedStaircaseBottomRowExpansion_four_two :
    truncatedStaircaseBottomRowExpansion 4 2 := by
  dsimp [truncatedStaircaseBottomRowExpansion]
  rw [show List.range 2 = [0, 1] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_four_three,
    truncatedStaircaseRookPolynomial_four_two,
    truncatedStaircaseRookPolynomial_three_two,
    truncatedStaircaseRookPolynomial_two_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 :=
    Polynomial.C_eq_natCast (R := ℝ) 14
  rw [hC3, hC4, hC5, hC6, hC7, hC9, hC14]
  ring_nf

/-- The expected three-row `n = 5` truncated-staircase computation follows
from the named bottom-row expansion predicate. -/
theorem truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion_statement
    (hbottom : truncatedStaircaseBottomRowExpansion 5 2) :
    truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3 :=
  truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
    rw [show List.range (5 - 2) = [0, 1, 2] by rfl] at hbottom
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom
    simpa [add_assoc] using hbottom)

/-- The expected four-row `n = 5` truncated-staircase computation follows
from the bottom-row expansion into three-row truncated staircases. -/
theorem truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion
    (h53 : truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (hbottom : truncatedStaircaseRookPolynomial 5 4 =
      truncatedStaircaseRookPolynomial 5 3 +
        X * (truncatedStaircaseRookPolynomial 4 3 +
          truncatedStaircaseRookPolynomial 3 3)) :
    truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 := by
  rw [hbottom, h53, truncatedStaircaseRookPolynomial_four_three,
    truncatedStaircaseRookPolynomial_three_three]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC9 : (C (9 : ℝ) : ℝ[X]) = 9 := Polynomial.C_eq_natCast (R := ℝ) 9
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
    Polynomial.C_eq_natCast (R := ℝ) 10
  have hC12 : (C (12 : ℝ) : ℝ[X]) = 12 :=
    Polynomial.C_eq_natCast (R := ℝ) 12
  have hC14 : (C (14 : ℝ) : ℝ[X]) = 14 :=
    Polynomial.C_eq_natCast (R := ℝ) 14
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  have hC30 : (C (30 : ℝ) : ℝ[X]) = 30 :=
    Polynomial.C_eq_natCast (R := ℝ) 30
  have hC40 : (C (40 : ℝ) : ℝ[X]) = 40 :=
    Polynomial.C_eq_natCast (R := ℝ) 40
  rw [hC4, hC5, hC6, hC9, hC10, hC12, hC14, hC25, hC30, hC40]
  ring_nf

/-- The expected four-row `n = 5` truncated-staircase computation follows
from the named bottom-row expansion predicate. -/
theorem truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion_statement
    (h53 : truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (hbottom : truncatedStaircaseBottomRowExpansion 5 3) :
    truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion h53 (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom
    rw [show List.range (5 - 3) = [0, 1] by rfl] at hbottom
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom
    simpa [add_assoc] using hbottom)

/-- The expected `G_5` finite-board value follows from the two bottom-row
expansions needed for the remaining `n = 5` truncated-staircase rows. -/
theorem auxiliaryG_five_of_bottom_row_expansions
    (hbottom53 : truncatedStaircaseRookPolynomial 5 3 =
      truncatedStaircaseRookPolynomial 5 2 +
        X * (truncatedStaircaseRookPolynomial 4 2 +
          truncatedStaircaseRookPolynomial 3 2 +
            truncatedStaircaseRookPolynomial 2 2))
    (hbottom54 : truncatedStaircaseRookPolynomial 5 4 =
      truncatedStaircaseRookPolynomial 5 3 +
        X * (truncatedStaircaseRookPolynomial 4 3 +
          truncatedStaircaseRookPolynomial 3 3)) :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  auxiliaryG_five_of_truncatedStaircaseRookPolynomial_five_three_four
    (truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion
      hbottom53)
    (truncatedStaircaseRookPolynomial_five_four_of_bottom_row_expansion
      (truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion
        hbottom53)
      hbottom54)

/-- The expected `G_5` finite-board value follows from the named bottom-row
expansion predicate in the two remaining `n = 5` rows. -/
theorem auxiliaryG_five_of_bottom_row_expansion_statements
    (hbottom53 : truncatedStaircaseBottomRowExpansion 5 2)
    (hbottom54 : truncatedStaircaseBottomRowExpansion 5 3) :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  auxiliaryG_five_of_bottom_row_expansions (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom53
    rw [show List.range (5 - 2) = [0, 1, 2] by rfl] at hbottom53
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom53
    simpa [add_assoc] using hbottom53) (by
    dsimp [truncatedStaircaseBottomRowExpansion] at hbottom54
    rw [show List.range (5 - 3) = [0, 1] by rfl] at hbottom54
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hbottom54
    simpa [add_assoc] using hbottom54)

/-- The three-row `n = 5` truncated-staircase rook polynomial. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_three :
    truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3 :=
  truncatedStaircaseRookPolynomial_five_three_of_bottom_row_expansion_statement
    (truncatedStaircaseBottomRowExpansion_all 5 2)

/-- The four-row `n = 5` truncated-staircase rook polynomial. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_four :
    truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 5 (by norm_num)]
  norm_num [Nat.choose]

/-- The finite-board auxiliary polynomial `G_5` is
`5 + 40X + 75X^2 + 40X^3 + 5X^4`. -/
@[simp] theorem auxiliaryG_five :
    auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4 :=
  auxiliaryG_five_of_bottom_row_expansion_statements
    (truncatedStaircaseBottomRowExpansion_all 5 2)
    (truncatedStaircaseBottomRowExpansion_all 5 3)

/-- The one-row truncated staircase with one cell has rook polynomial
`1 + X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_one_one :
    truncatedStaircaseRookPolynomial 1 1 = 1 + X := by
  rw [truncatedStaircaseRookPolynomial_one_row]
  norm_num

/-- The one-row truncated staircase with six cells has rook polynomial
`1 + 6X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_one :
    truncatedStaircaseRookPolynomial 6 1 = 1 + C (6 : ℝ) * X :=
  truncatedStaircaseRookPolynomial_one_row 6

/-- The two-row truncated staircase with row lengths six and five has rook
polynomial `1 + 11X + 15X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_two :
    truncatedStaircaseRookPolynomial 6 2 =
      1 + C (11 : ℝ) * X + C (15 : ℝ) * X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 :=
    Polynomial.C_eq_natCast (R := ℝ) 15
  rw [hC15]
  norm_num [Nat.choose]
  exact hC15

/-- The three-row truncated staircase with row lengths six, five, and four has
rook polynomial `1 + 15X + 39X^2 + 20X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_three :
    truncatedStaircaseRookPolynomial 6 3 =
      1 + C (15 : ℝ) * X + C (39 : ℝ) * X ^ 2 +
        C (20 : ℝ) * X ^ 3 := by
  rw [truncatedStaircaseRookPolynomial_three_rows 6 (by norm_num)]
  norm_num [Nat.choose]

/-- The four-row truncated staircase with row lengths four, three, two, and one
has rook polynomial `1 + 10X + 20X^2 + 10X^3 + X^4`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_four :
    truncatedStaircaseRookPolynomial 4 4 =
      1 + C (10 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
        C (10 : ℝ) * X ^ 3 + X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 4 (by norm_num)]
  norm_num [Nat.choose]

/-- The four-row truncated staircase with row lengths six, five, four, and
three has rook polynomial `1 + 18X + 66X^2 + 65X^3 + 15X^4`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_four :
    truncatedStaircaseRookPolynomial 6 4 =
      1 + C (18 : ℝ) * X + C (66 : ℝ) * X ^ 2 +
        C (65 : ℝ) * X ^ 3 + C (15 : ℝ) * X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 6 (by norm_num)]
  norm_num [Nat.choose]

/-- The five-row truncated staircase with row lengths six, five, four, three,
and two has rook polynomial
`1 + 20X + 90X^2 + 125X^3 + 55X^4 + 6X^5`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_six_five :
    truncatedStaircaseRookPolynomial 6 5 =
      1 + C (20 : ℝ) * X + C (90 : ℝ) * X ^ 2 +
        C (125 : ℝ) * X ^ 3 + C (55 : ℝ) * X ^ 4 +
          C (6 : ℝ) * X ^ 5 := by
  rw [truncatedStaircaseRookPolynomial_five_rows 6 (by norm_num)]
  norm_num [Nat.choose]

/-- The five-row truncated staircase with row lengths five, four, three, two,
and one has rook polynomial
`1 + 15X + 50X^2 + 50X^3 + 15X^4 + X^5`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_five :
    truncatedStaircaseRookPolynomial 5 5 =
      1 + C (15 : ℝ) * X + C (50 : ℝ) * X ^ 2 +
        C (50 : ℝ) * X ^ 3 + C (15 : ℝ) * X ^ 4 + X ^ 5 := by
  rw [truncatedStaircaseRookPolynomial_five_rows 5 (by norm_num)]
  norm_num [Nat.choose]

/-- The finite-board auxiliary polynomial `G_6` is
`6 + 70X + 210X^2 + 210X^3 + 70X^4 + 6X^5`. -/
@[simp] theorem auxiliaryG_six :
    auxiliaryG 6 =
      6 + C (70 : ℝ) * X + C (210 : ℝ) * X ^ 2 +
        C (210 : ℝ) * X ^ 3 + C (70 : ℝ) * X ^ 4 +
          C (6 : ℝ) * X ^ 5 := by
  rw [auxiliaryG, show List.range 6 = [0, 1, 2, 3, 4, 5] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_six_one,
    truncatedStaircaseRookPolynomial_six_two,
    truncatedStaircaseRookPolynomial_six_three,
    truncatedStaircaseRookPolynomial_six_four,
    truncatedStaircaseRookPolynomial_six_five]
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC11 : (C (11 : ℝ) : ℝ[X]) = 11 :=
    Polynomial.C_eq_natCast (R := ℝ) 11
  have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 :=
    Polynomial.C_eq_natCast (R := ℝ) 15
  have hC18 : (C (18 : ℝ) : ℝ[X]) = 18 :=
    Polynomial.C_eq_natCast (R := ℝ) 18
  have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 :=
    Polynomial.C_eq_natCast (R := ℝ) 20
  have hC39 : (C (39 : ℝ) : ℝ[X]) = 39 :=
    Polynomial.C_eq_natCast (R := ℝ) 39
  have hC55 : (C (55 : ℝ) : ℝ[X]) = 55 :=
    Polynomial.C_eq_natCast (R := ℝ) 55
  have hC65 : (C (65 : ℝ) : ℝ[X]) = 65 :=
    Polynomial.C_eq_natCast (R := ℝ) 65
  have hC66 : (C (66 : ℝ) : ℝ[X]) = 66 :=
    Polynomial.C_eq_natCast (R := ℝ) 66
  have hC70 : (C (70 : ℝ) : ℝ[X]) = 70 :=
    Polynomial.C_eq_natCast (R := ℝ) 70
  have hC90 : (C (90 : ℝ) : ℝ[X]) = 90 :=
    Polynomial.C_eq_natCast (R := ℝ) 90
  have hC125 : (C (125 : ℝ) : ℝ[X]) = 125 :=
    Polynomial.C_eq_natCast (R := ℝ) 125
  have hC210 : (C (210 : ℝ) : ℝ[X]) = 210 :=
    Polynomial.C_eq_natCast (R := ℝ) 210
  rw [hC6, hC11, hC15, hC18, hC20, hC39, hC55, hC65, hC66, hC70,
    hC90, hC125, hC210]
  ring_nf

/-- The one-row truncated staircase with seven cells has rook polynomial
`1 + 7X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_one :
    truncatedStaircaseRookPolynomial 7 1 = 1 + C (7 : ℝ) * X :=
  truncatedStaircaseRookPolynomial_one_row 7

/-- The two-row truncated staircase with row lengths seven and six has rook
polynomial `1 + 13X + 21X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_two :
    truncatedStaircaseRookPolynomial 7 2 =
      1 + C (13 : ℝ) * X + C (21 : ℝ) * X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  have hC21 : (C (21 : ℝ) : ℝ[X]) = 21 :=
    Polynomial.C_eq_natCast (R := ℝ) 21
  rw [hC21]
  norm_num [Nat.choose]
  exact hC21

/-- The three-row truncated staircase with row lengths seven, six, and five
has rook polynomial `1 + 18X + 56X^2 + 35X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_three :
    truncatedStaircaseRookPolynomial 7 3 =
      1 + C (18 : ℝ) * X + C (56 : ℝ) * X ^ 2 +
        C (35 : ℝ) * X ^ 3 := by
  rw [truncatedStaircaseRookPolynomial_three_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The four-row truncated staircase with row lengths seven, six, five, and
four has rook polynomial `1 + 22X + 98X^2 + 119X^3 + 35X^4`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_four :
    truncatedStaircaseRookPolynomial 7 4 =
      1 + C (22 : ℝ) * X + C (98 : ℝ) * X ^ 2 +
        C (119 : ℝ) * X ^ 3 + C (35 : ℝ) * X ^ 4 := by
  rw [truncatedStaircaseRookPolynomial_four_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The five-row truncated staircase with row lengths seven, six, five, four,
and three has rook polynomial
`1 + 25X + 140X^2 + 245X^3 + 140X^4 + 21X^5`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_five :
    truncatedStaircaseRookPolynomial 7 5 =
      1 + C (25 : ℝ) * X + C (140 : ℝ) * X ^ 2 +
        C (245 : ℝ) * X ^ 3 + C (140 : ℝ) * X ^ 4 +
          C (21 : ℝ) * X ^ 5 := by
  rw [truncatedStaircaseRookPolynomial_five_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The six-row truncated staircase with row lengths seven, six, five, four,
three, and two has rook polynomial
`1 + 27X + 175X^2 + 385X^3 + 315X^4 + 91X^5 + 7X^6`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_seven_six :
    truncatedStaircaseRookPolynomial 7 6 =
      1 + C (27 : ℝ) * X + C (175 : ℝ) * X ^ 2 +
        C (385 : ℝ) * X ^ 3 + C (315 : ℝ) * X ^ 4 +
          C (91 : ℝ) * X ^ 5 + C (7 : ℝ) * X ^ 6 := by
  rw [truncatedStaircaseRookPolynomial_six_rows 7 (by norm_num)]
  norm_num [Nat.choose]

/-- The finite-board auxiliary polynomial `G_7` is
`7 + 112X + 490X^2 + 784X^3 + 490X^4 + 112X^5 + 7X^6`. -/
@[simp] theorem auxiliaryG_seven :
    auxiliaryG 7 =
      7 + C (112 : ℝ) * X + C (490 : ℝ) * X ^ 2 +
        C (784 : ℝ) * X ^ 3 + C (490 : ℝ) * X ^ 4 +
          C (112 : ℝ) * X ^ 5 + C (7 : ℝ) * X ^ 6 := by
  rw [auxiliaryG, show List.range 7 = [0, 1, 2, 3, 4, 5, 6] by rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [truncatedStaircaseRookPolynomial_zero_rows,
    truncatedStaircaseRookPolynomial_seven_one,
    truncatedStaircaseRookPolynomial_seven_two,
    truncatedStaircaseRookPolynomial_seven_three,
    truncatedStaircaseRookPolynomial_seven_four,
    truncatedStaircaseRookPolynomial_seven_five,
    truncatedStaircaseRookPolynomial_seven_six]
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC13 : (C (13 : ℝ) : ℝ[X]) = 13 :=
    Polynomial.C_eq_natCast (R := ℝ) 13
  have hC18 : (C (18 : ℝ) : ℝ[X]) = 18 :=
    Polynomial.C_eq_natCast (R := ℝ) 18
  have hC21 : (C (21 : ℝ) : ℝ[X]) = 21 :=
    Polynomial.C_eq_natCast (R := ℝ) 21
  have hC22 : (C (22 : ℝ) : ℝ[X]) = 22 :=
    Polynomial.C_eq_natCast (R := ℝ) 22
  have hC25 : (C (25 : ℝ) : ℝ[X]) = 25 :=
    Polynomial.C_eq_natCast (R := ℝ) 25
  have hC27 : (C (27 : ℝ) : ℝ[X]) = 27 :=
    Polynomial.C_eq_natCast (R := ℝ) 27
  have hC35 : (C (35 : ℝ) : ℝ[X]) = 35 :=
    Polynomial.C_eq_natCast (R := ℝ) 35
  have hC56 : (C (56 : ℝ) : ℝ[X]) = 56 :=
    Polynomial.C_eq_natCast (R := ℝ) 56
  have hC91 : (C (91 : ℝ) : ℝ[X]) = 91 :=
    Polynomial.C_eq_natCast (R := ℝ) 91
  have hC98 : (C (98 : ℝ) : ℝ[X]) = 98 :=
    Polynomial.C_eq_natCast (R := ℝ) 98
  have hC112 : (C (112 : ℝ) : ℝ[X]) = 112 :=
    Polynomial.C_eq_natCast (R := ℝ) 112
  have hC119 : (C (119 : ℝ) : ℝ[X]) = 119 :=
    Polynomial.C_eq_natCast (R := ℝ) 119
  have hC140 : (C (140 : ℝ) : ℝ[X]) = 140 :=
    Polynomial.C_eq_natCast (R := ℝ) 140
  have hC175 : (C (175 : ℝ) : ℝ[X]) = 175 :=
    Polynomial.C_eq_natCast (R := ℝ) 175
  have hC245 : (C (245 : ℝ) : ℝ[X]) = 245 :=
    Polynomial.C_eq_natCast (R := ℝ) 245
  have hC315 : (C (315 : ℝ) : ℝ[X]) = 315 :=
    Polynomial.C_eq_natCast (R := ℝ) 315
  have hC385 : (C (385 : ℝ) : ℝ[X]) = 385 :=
    Polynomial.C_eq_natCast (R := ℝ) 385
  have hC490 : (C (490 : ℝ) : ℝ[X]) = 490 :=
    Polynomial.C_eq_natCast (R := ℝ) 490
  have hC784 : (C (784 : ℝ) : ℝ[X]) = 784 :=
    Polynomial.C_eq_natCast (R := ℝ) 784
  rw [hC7, hC13, hC18, hC21, hC22, hC25, hC27, hC35, hC56, hC91,
    hC98, hC112, hC119, hC140, hC175, hC245, hC315, hC385, hC490,
    hC784]
  ring_nf

/-- The finite-board version of `G_n` has nonnegative coefficients. -/
theorem auxiliaryG_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (auxiliaryG n) := by
  refine listSum_hasNonnegCoeffs ?_
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _hi, rfl⟩
  exact rookPolynomial_hasNonnegCoeffs _

end FiniteSkewBoard

end GeneralizedSnakePosets
end RealRooted
