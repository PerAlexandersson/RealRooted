import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.RowFormulas

/-!
# Explicit finite truncated-staircase cases

This module records the small truncated-staircase rook polynomials used by
the finite Braun--Jal recurrence checks, as instances of the row formulas in
`RealRooted.GeneralizedSnakePosets.TruncatedStaircase.RowFormulas`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

/-- The one-row truncated staircase with two cells has rook polynomial
`1 + 2X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_two_one :
    truncatedStaircaseRookPolynomial 2 1 = 1 + C (2 : ℝ) * X := by
  simp

/-- The one-row truncated staircase with three cells has rook polynomial
`1 + 3X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_one :
    truncatedStaircaseRookPolynomial 3 1 = 1 + C (3 : ℝ) * X := by
  simp

/-- The one-row truncated staircase with four cells has rook polynomial
`1 + 4X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_one :
    truncatedStaircaseRookPolynomial 4 1 = 1 + C (4 : ℝ) * X := by
  simp

/-- The one-row truncated staircase with five cells has rook polynomial
`1 + 5X`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_one :
    truncatedStaircaseRookPolynomial 5 1 = 1 + C (5 : ℝ) * X := by
  simp

/-- The two-row truncated staircase with row lengths two and one has rook
polynomial `1 + 3X + X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_two_two :
    truncatedStaircaseRookPolynomial 2 2 =
      1 + C (3 : ℝ) * X + X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  norm_num [Nat.choose]

/-- The two-row truncated staircase with row lengths three and two has rook
polynomial `1 + 5X + 3X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_two :
    truncatedStaircaseRookPolynomial 3 2 =
      1 + C (5 : ℝ) * X + C (3 : ℝ) * X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  norm_num [Nat.choose]

/-- The two-row truncated staircase with row lengths four and three has rook
polynomial `1 + 7X + 6X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_two :
    truncatedStaircaseRookPolynomial 4 2 =
      1 + C (7 : ℝ) * X + C (6 : ℝ) * X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  norm_num [Nat.choose]

/-- The two-row truncated staircase with row lengths five and four has rook
polynomial `1 + 9X + 10X^2`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_five_two :
    truncatedStaircaseRookPolynomial 5 2 =
      1 + C (9 : ℝ) * X + C (10 : ℝ) * X ^ 2 := by
  rw [truncatedStaircaseRookPolynomial_two_rows]
  norm_num [Nat.choose]

/-- The three-row truncated staircase with row lengths three, two, and one
has rook polynomial `1 + 6X + 6X^2 + X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_three_three :
    truncatedStaircaseRookPolynomial 3 3 =
      1 + C (6 : ℝ) * X + C (6 : ℝ) * X ^ 2 + X ^ 3 := by
  rw [truncatedStaircaseRookPolynomial_three_rows 3 (by norm_num)]
  norm_num [Nat.choose]

/-- The three-row truncated staircase with row lengths four, three, and two
has rook polynomial `1 + 9X + 14X^2 + 4X^3`. -/
@[simp] theorem truncatedStaircaseRookPolynomial_four_three :
    truncatedStaircaseRookPolynomial 4 3 =
      1 + C (9 : ℝ) * X + C (14 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3 := by
  rw [truncatedStaircaseRookPolynomial_three_rows 4 (by norm_num)]
  norm_num [Nat.choose]

end FiniteSkewBoard
end GeneralizedSnakePosets
end RealRooted
