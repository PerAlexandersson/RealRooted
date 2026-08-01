import RealRooted.Combinatorics.OrderedSubsetPairsNarayana
import RealRooted.GeneralizedSnakePosets.Narayana.Modified
import RealRooted.GeneralizedSnakePosets.Narayana.TuranCertificates

/-!
# Narayana inputs for generalized snake posets

This module connects the Braun--Jal generalized-snake-poset statement
interfaces to the existing Narayana polynomial formalization.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Full truncated-staircase Narayana coefficients -/

/-- Size-`k` non-nesting placements in the full truncated staircase are counted
by the `m = 1` Narayana coefficient. -/
theorem FiniteSkewBoard.card_fullStaircasePlacements_eq_narayanaTransformCoeff_one
    (n k : ℕ) :
    (((FiniteSkewBoard.truncatedStaircase n n).nonNestingPlacements.filter
        fun P => P.card = k).card : ℝ) =
      narayanaTransformCoeff 1 n k := by
  rw [FiniteSkewBoard.card_fullStaircasePlacements_eq_orderedKSubsetPairs]
  exact Finset.card_orderedKSubsetPairs_eq_narayanaTransformCoeff_one n k

/-- The full truncated-staircase rook-polynomial coefficients are the
`m = 1` Narayana coefficients. -/
theorem FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_narayanaTransformCoeff_one
    (n k : ℕ) :
    (FiniteSkewBoard.truncatedStaircaseRookPolynomial n n).coeff k =
      narayanaTransformCoeff 1 n k := by
  rw [FiniteSkewBoard.truncatedStaircaseRookPolynomial,
    FiniteSkewBoard.rookPolynomial_coeff]
  exact FiniteSkewBoard.card_fullStaircasePlacements_eq_narayanaTransformCoeff_one n k

/-- The full truncated-staircase rook polynomial and the coefficient-side
modified Narayana polynomial have the same coefficients. -/
theorem FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaCoeff
    (n k : ℕ) :
    (FiniteSkewBoard.truncatedStaircaseRookPolynomial n n).coeff k =
      (modifiedNarayanaCoeffPolynomial n).coeff k := by
  rw [FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_narayanaTransformCoeff_one,
    modifiedNarayanaCoeffPolynomial]
  by_cases hk : k ≤ n
  · rw [coeff_narayanaPolynomial_of_le (m := 1) hk]
  · have hklt : n < k := Nat.lt_of_not_ge hk
    rw [coeff_narayanaPolynomial_of_lt (m := 1) hklt,
      narayanaTransformCoeff_eq_zero_of_lt (m := 1) hklt]

/-- The full truncated-staircase rook polynomial is the modified Narayana
polynomial. -/
theorem FiniteSkewBoard.truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial
    (n : ℕ) :
    FiniteSkewBoard.truncatedStaircaseRookPolynomial n n =
      modifiedNarayanaPolynomial n := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial]
  ext k
  exact
    FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaCoeff
      n k

/-- The `n = 2` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_two :
    X * FiniteSkewBoard.auxiliaryG 1 =
      modifiedNarayanaPolynomial 2 -
        (1 + X) * modifiedNarayanaPolynomial 1 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 1,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 2]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_two

/-- The `n = 3` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_three :
    X * FiniteSkewBoard.auxiliaryG 2 =
      modifiedNarayanaPolynomial 3 -
        (1 + X) * modifiedNarayanaPolynomial 2 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 2,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 3]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_three

/-- The `n = 4` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the concrete `G_3` finite-board computation. -/
theorem narayanaAuxiliaryGRecurrence_modified_four_of_auxiliaryG_three
    (hG3 : FiniteSkewBoard.auxiliaryG 3 =
      3 + C (8 : ℝ) * X + C (3 : ℝ) * X ^ 2) :
    X * FiniteSkewBoard.auxiliaryG 3 =
      modifiedNarayanaPolynomial 4 -
        (1 + X) * modifiedNarayanaPolynomial 3 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 3,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 4]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_four_of_auxiliaryG_three hG3

/-- The `n = 4` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_four :
    X * FiniteSkewBoard.auxiliaryG 3 =
      modifiedNarayanaPolynomial 4 -
        (1 + X) * modifiedNarayanaPolynomial 3 :=
  narayanaAuxiliaryGRecurrence_modified_four_of_auxiliaryG_three
    FiniteSkewBoard.auxiliaryG_three

/-- The `n = 5` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the concrete `G_4` finite-board computation. -/
theorem narayanaAuxiliaryGRecurrence_modified_five_of_auxiliaryG_four
    (hG4 : FiniteSkewBoard.auxiliaryG 4 =
      4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    X * FiniteSkewBoard.auxiliaryG 4 =
      modifiedNarayanaPolynomial 5 -
        (1 + X) * modifiedNarayanaPolynomial 4 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 4,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 5]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_five_of_auxiliaryG_four hG4

/-- The `n = 5` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_five :
    X * FiniteSkewBoard.auxiliaryG 4 =
      modifiedNarayanaPolynomial 5 -
        (1 + X) * modifiedNarayanaPolynomial 4 :=
  narayanaAuxiliaryGRecurrence_modified_five_of_auxiliaryG_four
    FiniteSkewBoard.auxiliaryG_four

/-- The `n = 6` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the concrete `G_5` finite-board computation. -/
theorem narayanaAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (hG5 : FiniteSkewBoard.auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4) :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaPolynomial 6 -
        (1 + X) * modifiedNarayanaPolynomial 5 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 5,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 6]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five hG5

/-- The `n = 6` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the remaining three-row and four-row
truncated-staircase rook-polynomial computations. -/
theorem narayanaAuxiliaryGRecurrence_modified_six_of_staircase_five_tail
    (h53 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (h54 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4) :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaPolynomial 6 -
        (1 + X) * modifiedNarayanaPolynomial 5 :=
  narayanaAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_truncatedStaircaseRookPolynomial_five_three_four
      h53 h54)

/-- The `n = 6` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the bottom-row expansions for the two remaining
`n = 5` truncated-staircase rook-polynomial rows. -/
theorem narayanaAuxiliaryGRecurrence_modified_six_of_bottom_row_expansions
    (hbottom53 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 3 =
      FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 2 +
        X * (FiniteSkewBoard.truncatedStaircaseRookPolynomial 4 2 +
          FiniteSkewBoard.truncatedStaircaseRookPolynomial 3 2 +
            FiniteSkewBoard.truncatedStaircaseRookPolynomial 2 2))
    (hbottom54 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 4 =
      FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 3 +
        X * (FiniteSkewBoard.truncatedStaircaseRookPolynomial 4 3 +
          FiniteSkewBoard.truncatedStaircaseRookPolynomial 3 3)) :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaPolynomial 6 -
        (1 + X) * modifiedNarayanaPolynomial 5 :=
  narayanaAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_bottom_row_expansions
      hbottom53 hbottom54)

/-- The `n = 6` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the named bottom-row expansion predicate for the
two remaining `n = 5` truncated-staircase rows. -/
theorem narayanaAuxiliaryGRecurrence_modified_six_of_bottom_row_expansion_statements
    (hbottom53 : FiniteSkewBoard.truncatedStaircaseBottomRowExpansion 5 2)
    (hbottom54 : FiniteSkewBoard.truncatedStaircaseBottomRowExpansion 5 3) :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaPolynomial 6 -
        (1 + X) * modifiedNarayanaPolynomial 5 :=
  narayanaAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_bottom_row_expansion_statements
      hbottom53 hbottom54)

/-- The `n = 6` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_six :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaPolynomial 6 -
        (1 + X) * modifiedNarayanaPolynomial 5 :=
  narayanaAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    FiniteSkewBoard.auxiliaryG_five

/-- The `n = 7` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the concrete `G_6` finite-board computation. -/
theorem narayanaAuxiliaryGRecurrence_modified_seven_of_auxiliaryG_six
    (hG6 : FiniteSkewBoard.auxiliaryG 6 =
      6 + C (70 : ℝ) * X + C (210 : ℝ) * X ^ 2 +
        C (210 : ℝ) * X ^ 3 + C (70 : ℝ) * X ^ 4 +
          C (6 : ℝ) * X ^ 5) :
    X * FiniteSkewBoard.auxiliaryG 6 =
      modifiedNarayanaPolynomial 7 -
        (1 + X) * modifiedNarayanaPolynomial 6 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 6,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 7]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_seven_of_auxiliaryG_six hG6

/-- The `n = 7` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_seven :
    X * FiniteSkewBoard.auxiliaryG 6 =
      modifiedNarayanaPolynomial 7 -
        (1 + X) * modifiedNarayanaPolynomial 6 :=
  narayanaAuxiliaryGRecurrence_modified_seven_of_auxiliaryG_six
    FiniteSkewBoard.auxiliaryG_six

/-- The `n = 8` Braun--Jal equation (2), for the quotient-style modified
Narayana family, reduces to the concrete `G_7` finite-board computation. -/
theorem narayanaAuxiliaryGRecurrence_modified_eight_of_auxiliaryG_seven
    (hG7 : FiniteSkewBoard.auxiliaryG 7 =
      7 + C (112 : ℝ) * X + C (490 : ℝ) * X ^ 2 +
        C (784 : ℝ) * X ^ 3 + C (490 : ℝ) * X ^ 4 +
          C (112 : ℝ) * X ^ 5 + C (7 : ℝ) * X ^ 6) :
    X * FiniteSkewBoard.auxiliaryG 7 =
      modifiedNarayanaPolynomial 8 -
        (1 + X) * modifiedNarayanaPolynomial 7 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 7,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 8]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_eight_of_auxiliaryG_seven hG7

/-- The `n = 8` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_eight :
    X * FiniteSkewBoard.auxiliaryG 7 =
      modifiedNarayanaPolynomial 8 -
        (1 + X) * modifiedNarayanaPolynomial 7 :=
  narayanaAuxiliaryGRecurrence_modified_eight_of_auxiliaryG_seven
    FiniteSkewBoard.auxiliaryG_seven

/-- The checked initial cases `n = 1, 2` of Braun--Jal equation (2), for the
quotient-style modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_two
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 2) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaAuxiliaryGRecurrence_modified_base
  · exact narayanaAuxiliaryGRecurrence_modified_two

/-- The checked initial cases `n = 1, 2, 3` of Braun--Jal equation (2), for the
quotient-style modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_three
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaAuxiliaryGRecurrence_modified_base
  · exact narayanaAuxiliaryGRecurrence_modified_two
  · exact narayanaAuxiliaryGRecurrence_modified_three

/-- The checked initial cases `n = 1, 2, 3`, plus the conditional `n = 4` case
of Braun--Jal equation (2), for the quotient-style modified Narayana family and
the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_four_of_auxiliaryG_three
    (hG3 : FiniteSkewBoard.auxiliaryG 3 =
      3 + C (8 : ℝ) * X + C (3 : ℝ) * X ^ 2)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₄ : n ≤ 4) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaAuxiliaryGRecurrence_modified_base
  · exact narayanaAuxiliaryGRecurrence_modified_two
  · exact narayanaAuxiliaryGRecurrence_modified_three
  · exact narayanaAuxiliaryGRecurrence_modified_four_of_auxiliaryG_three hG3

/-- The checked initial cases `n = 1, 2, 3, 4` of Braun--Jal equation (2),
for the quotient-style modified Narayana family and the finite-board
auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_four
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₄ : n ≤ 4) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  exact narayanaAuxiliaryGRecurrence_modified_of_le_four_of_auxiliaryG_three
    FiniteSkewBoard.auxiliaryG_three hn₁ hn₄

/-- The checked initial cases `n = 1, 2, 3, 4`, plus the conditional `n = 5`
case of Braun--Jal equation (2), for the quotient-style modified Narayana
family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_five_of_auxiliaryG_four
    (hG4 : FiniteSkewBoard.auxiliaryG 4 =
      4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₅ : n ≤ 5) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaAuxiliaryGRecurrence_modified_base
  · exact narayanaAuxiliaryGRecurrence_modified_two
  · exact narayanaAuxiliaryGRecurrence_modified_three
  · exact narayanaAuxiliaryGRecurrence_modified_four
  · exact narayanaAuxiliaryGRecurrence_modified_five_of_auxiliaryG_four hG4

/-- The checked initial cases `n = 1, 2, 3, 4, 5` of Braun--Jal equation (2),
for the quotient-style modified Narayana family and the finite-board
auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_five
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₅ : n ≤ 5) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  exact narayanaAuxiliaryGRecurrence_modified_of_le_five_of_auxiliaryG_four
    FiniteSkewBoard.auxiliaryG_four hn₁ hn₅

/-- The checked initial cases `n = 1, 2, 3, 4, 5`, plus the conditional `n = 6`
case of Braun--Jal equation (2), for the quotient-style modified Narayana
family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_six_of_auxiliaryG_five
    (hG5 : FiniteSkewBoard.auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaAuxiliaryGRecurrence_modified_base
  · exact narayanaAuxiliaryGRecurrence_modified_two
  · exact narayanaAuxiliaryGRecurrence_modified_three
  · exact narayanaAuxiliaryGRecurrence_modified_four
  · exact narayanaAuxiliaryGRecurrence_modified_five
  · exact narayanaAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five hG5

/-- The checked initial cases through `n = 6`, reducing the last case to the
remaining three-row and four-row truncated-staircase computations. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_six_of_staircase_five_tail
    (h53 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (h54 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) :=
  narayanaAuxiliaryGRecurrence_modified_of_le_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_truncatedStaircaseRookPolynomial_five_three_four
      h53 h54)
    hn₁ hn₆

/-- The checked initial cases through `n = 6`, reducing the last case to the
bottom-row expansions for the two remaining `n = 5` truncated-staircase
rook-polynomial rows. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_six_of_bottom_row_expansions
    (hbottom53 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 3 =
      FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 2 +
        X * (FiniteSkewBoard.truncatedStaircaseRookPolynomial 4 2 +
          FiniteSkewBoard.truncatedStaircaseRookPolynomial 3 2 +
            FiniteSkewBoard.truncatedStaircaseRookPolynomial 2 2))
    (hbottom54 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 4 =
      FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 3 +
        X * (FiniteSkewBoard.truncatedStaircaseRookPolynomial 4 3 +
          FiniteSkewBoard.truncatedStaircaseRookPolynomial 3 3))
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) :=
  narayanaAuxiliaryGRecurrence_modified_of_le_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_bottom_row_expansions
      hbottom53 hbottom54)
    hn₁ hn₆

/-- The checked initial cases through `n = 6`, reducing the last case to the
named bottom-row expansion predicate for the two remaining `n = 5`
truncated-staircase rows. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_six_of_bottom_row_expansion_statements
    (hbottom53 : FiniteSkewBoard.truncatedStaircaseBottomRowExpansion 5 2)
    (hbottom54 : FiniteSkewBoard.truncatedStaircaseBottomRowExpansion 5 3)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) :=
  narayanaAuxiliaryGRecurrence_modified_of_le_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_bottom_row_expansion_statements
      hbottom53 hbottom54)
    hn₁ hn₆

/-- The checked initial cases through `n = 6` of Braun--Jal equation (2), for
the quotient-style modified Narayana family and finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_six
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) :=
  narayanaAuxiliaryGRecurrence_modified_of_le_six_of_auxiliaryG_five
    FiniteSkewBoard.auxiliaryG_five hn₁ hn₆

/-- The checked initial cases through `n = 7` of Braun--Jal equation (2), for
the quotient-style modified Narayana family and finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_seven
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₇ : n ≤ 7) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaAuxiliaryGRecurrence_modified_base
  · exact narayanaAuxiliaryGRecurrence_modified_two
  · exact narayanaAuxiliaryGRecurrence_modified_three
  · exact narayanaAuxiliaryGRecurrence_modified_four
  · exact narayanaAuxiliaryGRecurrence_modified_five
  · exact narayanaAuxiliaryGRecurrence_modified_six
  · exact narayanaAuxiliaryGRecurrence_modified_seven

/-- The checked initial cases through `n = 8` of Braun--Jal equation (2), for
the quotient-style modified Narayana family and finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_of_le_eight
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₈ : n ≤ 8) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n -
        (1 + X) * modifiedNarayanaPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaAuxiliaryGRecurrence_modified_base
  · exact narayanaAuxiliaryGRecurrence_modified_two
  · exact narayanaAuxiliaryGRecurrence_modified_three
  · exact narayanaAuxiliaryGRecurrence_modified_four
  · exact narayanaAuxiliaryGRecurrence_modified_five
  · exact narayanaAuxiliaryGRecurrence_modified_six
  · exact narayanaAuxiliaryGRecurrence_modified_seven
  · exact narayanaAuxiliaryGRecurrence_modified_eight

/-- The checked initial cases `n = 1, ..., 8` of Braun--Jal equation (2),
packaged in the generic bounded recurrence interface. -/
theorem narayanaAuxiliaryGRecurrence_modified_upTo_eight :
    NarayanaAuxiliaryGRecurrenceUpToStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG 8 := by
  intro n hn₁ hn₈
  exact narayanaAuxiliaryGRecurrence_modified_of_le_eight hn₁ hn₈

/-- Unconditional consecutive proper position for the modified Narayana
family. -/
theorem modifiedNarayanaPolynomial_prec_succ (n : ℕ) :
    Prec (modifiedNarayanaPolynomial n) (modifiedNarayanaPolynomial (n + 1)) :=
  modifiedNarayanaPolynomial_prec_succ_of_nonnegCoeffs n
    narayanaQuot_hasNonnegCoeffs

/-- Unconditional consecutive interlacing for the modified Narayana family. -/
theorem modifiedNarayanaPolynomial_interlaces_succ (n : ℕ) :
    Interlaces (modifiedNarayanaPolynomial n)
      (modifiedNarayanaPolynomial (n + 1)) :=
  modifiedNarayanaPolynomial_interlaces_succ_of_nonnegCoeffs n
    narayanaQuot_hasNonnegCoeffs

/-- Concrete modified-Narayana/auxiliary-`G` route for Braun--Jal Theorem 4.1.

This discharges the standard modified-Narayana facts and the elementary
auxiliary-`G` facts from the generic Section 3 route.  The remaining hypotheses
are the all-`n` equation `(2)`, Claim `(7)` side conditions, adjacent
interlacing of the auxiliary `G` column, and the word-family side conditions.
-/
theorem theorem41InductionRoute_modified_of_section3_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]}
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hside :
      Theorem41Claim7SideConditions
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hG : ∀ {m : ℕ}, 2 ≤ m →
      Prec (FiniteSkewBoard.auxiliaryG (m - 1)) (FiniteSkewBoard.auxiliaryG m))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const :
      ∀ {w : SnakeWord}, w.IsConstant →
        M w = modifiedNarayanaPolynomial (w.length + 1)) :
    Theorem41InductionRouteStatement
      M modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  theorem41InductionRoute_of_section3_of_constant_matches_succ_length
    (M := M) (P := modifiedNarayanaPolynomial) (G := FiniteSkewBoard.auxiliaryG)
    hrec2 hside modifiedNarayanaPolynomial_interlaces_succ hG
    modifiedNarayanaPolynomial_one FiniteSkewBoard.auxiliaryG_one
    modifiedNarayanaPolynomial_hasNonnegCoeffs
    FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs hM_nonneg hdeg hM_const

/-- Endpoint-compatible modified-Narayana route for Braun--Jal Theorem 4.1,
using root sums to orient Claim `(7)`. -/
theorem theorem41InductionRoute_modified_of_section3_rootSum_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]}
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hside :
      Theorem41Claim7RootSumSideConditions
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hG : ∀ {m : ℕ}, 2 ≤ m →
      Prec (FiniteSkewBoard.auxiliaryG (m - 1)) (FiniteSkewBoard.auxiliaryG m))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const :
      ∀ {w : SnakeWord}, w.IsConstant →
        M w = modifiedNarayanaPolynomial (w.length + 1)) :
    Theorem41InductionRouteStatement
      M modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  theorem41InductionRoute_of_section3_rootSum_of_constant_matches_succ_length
    (M := M) (P := modifiedNarayanaPolynomial) (G := FiniteSkewBoard.auxiliaryG)
    hrec2 hside modifiedNarayanaPolynomial_interlaces_succ hG
    modifiedNarayanaPolynomial_one FiniteSkewBoard.auxiliaryG_one
    modifiedNarayanaPolynomial_hasNonnegCoeffs
    FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs hM_nonneg hdeg hM_const

/-- Boundary polynomial showing that the strict negative `U`-root bound in the
current Claim `(7)` side-condition bundle cannot be discharged uniformly at
`ν = -1`. -/
theorem theorem41Claim7_modified_left_boundary_eq :
    (C (0 : ℝ) * X + C (-1 : ℝ)) * modifiedNarayanaPolynomial (2 - 1) +
        modifiedNarayanaPolynomial 2 =
      -X + C (3 : ℝ) * X + X ^ 2 := by
  norm_num [modifiedNarayanaPolynomial_one, modifiedNarayanaPolynomial_two]
  ring_nf

/-- In the boundary case `m = 2`, `λ = 0`, `ν = -1`, the left polynomial
`U = (λ X + ν) P_{m-1} + P_m` has zero as a root. -/
theorem theorem41Claim7_modified_left_boundary_isRoot_zero :
    ((C (0 : ℝ) * X + C (-1 : ℝ)) * modifiedNarayanaPolynomial (2 - 1) +
        modifiedNarayanaPolynomial 2).IsRoot 0 := by
  rw [theorem41Claim7_modified_left_boundary_eq, Polynomial.IsRoot.def]
  simp

/-- The strict negative upper bound requested by the current Claim `(7)` side
condition fails for the modified Narayana boundary case `λ = 0`, `ν = -1`. -/
theorem theorem41Claim7_modified_left_boundary_not_strictRootBound :
    ¬ ∃ c : ℝ,
      (∀ s ∈ (((C (0 : ℝ) * X + C (-1 : ℝ)) *
        modifiedNarayanaPolynomial (2 - 1) + modifiedNarayanaPolynomial 2).roots),
          s ≤ c) ∧ c < 0 := by
  rintro ⟨c, hle, hc⟩
  have hpoly_ne : -X + C (3 : ℝ) * X + X ^ 2 ≠ 0 := by
    intro h
    have heval := congr_arg (fun p : ℝ[X] => p.eval 1) h
    norm_num at heval
  have hboundary_ne :
      (C (0 : ℝ) * X + C (-1 : ℝ)) *
          modifiedNarayanaPolynomial (2 - 1) + modifiedNarayanaPolynomial 2 ≠
        0 := by
    rw [theorem41Claim7_modified_left_boundary_eq]
    exact hpoly_ne
  have hzero_mem :
      (0 : ℝ) ∈ (((C (0 : ℝ) * X + C (-1 : ℝ)) *
        modifiedNarayanaPolynomial (2 - 1) + modifiedNarayanaPolynomial 2).roots) :=
    (Polynomial.mem_roots hboundary_ne).mpr
      theorem41Claim7_modified_left_boundary_isRoot_zero
  have hzero_le : (0 : ℝ) ≤ c := hle 0 hzero_mem
  linarith

/-- Consequently, the current bundled Claim `(7)` side-condition interface is
not satisfiable by the concrete modified-Narayana / auxiliary-`G` data.  The
endpoint `ν = -1` needs a refined conversion route instead of a uniform strict
negative bound on the roots of `U`. -/
theorem not_theorem41Claim7SideConditions_modified_auxiliaryG :
    ¬ Theorem41Claim7SideConditions
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG := by
  intro hside
  exact theorem41Claim7_modified_left_boundary_not_strictRootBound
    (hside.u_bound (m := 2) (lam := 0) (nu := -1)
      (by norm_num) (by norm_num) (by norm_num))

/-- The concrete `G_2` auxiliary polynomial is twice `P_1`. -/
theorem auxiliaryG_two_eq_C_mul_modifiedNarayanaPolynomial_one :
    FiniteSkewBoard.auxiliaryG 2 =
      C (2 : ℝ) * modifiedNarayanaPolynomial 1 := by
  rw [FiniteSkewBoard.auxiliaryG_two, modifiedNarayanaPolynomial_one]
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
  rw [hC2]
  ring_nf

/-- The `n = 2` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_two :
    Prec (FiniteSkewBoard.auxiliaryG 2) (modifiedNarayanaPolynomial 2) := by
  rw [auxiliaryG_two_eq_C_mul_modifiedNarayanaPolynomial_one]
  exact (modifiedNarayanaPolynomial_prec_succ 1).C_mul_left (by norm_num)

/-- The checked initial cases `n = 1, 2` of Braun--Jal Lemma 3.3, for the
concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_two
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 2) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two

/-- The `λ = ν = 0` specialization of Braun--Jal Lemma 3.4 for the concrete
modified Narayana family.  This exposes the Lemma 3.4 target shape while using
the checked consecutive proper-position theorem. -/
theorem lemma34ModifiedNarayanaInterlacing_modified_zero_zero
    {m : ℕ} (_hm : 2 ≤ m) :
    Prec ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)) := by
  simpa using modifiedNarayanaPolynomial_prec_succ m

/-- The shifted `λ = 0, μ = 1` specialization of Braun--Jal Lemma 3.4 for the
concrete modified Narayana family. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_modified_zero_one
    {m : ℕ} (hm : 2 ≤ m) :
    Prec ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
        narayanaDifference modifiedNarayanaPolynomial m)
      ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial m +
        narayanaDifference modifiedNarayanaPolynomial (m + 1)) := by
  have hbase := lemma34ModifiedNarayanaInterlacing_modified_zero_zero hm
  have hleft :
      ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
          narayanaDifference modifiedNarayanaPolynomial m) =
        ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial (m - 1) +
          modifiedNarayanaPolynomial m) := by
    rw [narayanaDifference]
    simp
  have hright :
      ((C (0 : ℝ) * X + C (1 : ℝ)) * modifiedNarayanaPolynomial m +
          narayanaDifference modifiedNarayanaPolynomial (m + 1)) =
        ((C (0 : ℝ) * X + C (0 : ℝ)) * modifiedNarayanaPolynomial m +
          modifiedNarayanaPolynomial (m + 1)) := by
    rw [narayanaDifference]
    simp only [Nat.add_sub_cancel]
    simp
  rwa [hleft, hright]

/-- Concrete modified-Narayana wrapper: the shifted Lemma 3.4 target implies
the paper-shaped Lemma 3.4 target. -/
theorem lemma34ModifiedNarayanaInterlacing_modified_of_shifted
    (h :
      Lemma34ModifiedNarayanaShiftedInterlacingStatement
        modifiedNarayanaPolynomial) :
    Lemma34ModifiedNarayanaInterlacingStatement modifiedNarayanaPolynomial :=
  lemma34ModifiedNarayanaInterlacing_of_shifted h

/-- Concrete modified-Narayana wrapper: the paper-shaped Lemma 3.4 target
implies the shifted nonnegative-parameter target. -/
theorem lemma34ModifiedNarayanaShiftedInterlacing_modified_of_lemma34
    (h : Lemma34ModifiedNarayanaInterlacingStatement modifiedNarayanaPolynomial) :
    Lemma34ModifiedNarayanaShiftedInterlacingStatement
      modifiedNarayanaPolynomial :=
  lemma34ModifiedNarayanaShiftedInterlacing_of_lemma34 h

/-- The coefficient-side modified Narayana family also satisfies the
Braun--Jal modified-family interface. -/
theorem modifiedNarayanaFamily_coeff :
    ModifiedNarayanaFamilyStatement narayana modifiedNarayanaCoeffPolynomial := by
  constructor
  · simp
  · intro n
    rw [← modifiedNarayanaPolynomial_eq_coeffPolynomial]
    exact modifiedNarayanaFamily_narayana.2 n

/-- Coefficient-side modified Narayana polynomials are PF polynomials. -/
theorem modifiedNarayanaCoeffPolynomial_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (modifiedNarayanaCoeffPolynomial n) := by
  simpa [modifiedNarayanaCoeffPolynomial] using
    narayanaPolynomialRootLocation 1 n

/-- Modified Narayana polynomials are PF polynomials. -/
theorem modifiedNarayanaPolynomial_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (modifiedNarayanaPolynomial n) := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial n]
  exact modifiedNarayanaCoeffPolynomial_isPFPolynomial n

/-- Modified Narayana polynomials split over the reals. -/
theorem modifiedNarayanaPolynomial_splits (n : ℕ) :
    (modifiedNarayanaPolynomial n).Splits :=
  (modifiedNarayanaPolynomial_isPFPolynomial n).ne_zero_and_splits
    (modifiedNarayanaPolynomial_ne_zero n) |>.2

/-- The `P_6` modified Narayana polynomial splits over `ℝ`. -/
theorem modifiedNarayanaPolynomial_six_splits : (modifiedNarayanaPolynomial 6).Splits :=
  modifiedNarayanaPolynomial_splits 6

/-- The `P_6` modified Narayana polynomial has a sorted six-root list. -/
theorem modifiedNarayanaPolynomial_six_exists_ordered_roots :
    ∃ a b c d e r : ℝ,
      (modifiedNarayanaPolynomial 6).roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ) ∧
        a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧ e ≤ r := by
  let rs := (modifiedNarayanaPolynomial 6).roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = (modifiedNarayanaPolynomial 6).roots :=
    Multiset.sort_eq ..
  have hlen : rs.length = 6 := by
    rw [← Multiset.coe_card, hrs_eq,
      card_roots_of_splits modifiedNarayanaPolynomial_six_splits]
    exact modifiedNarayanaPolynomial_six_natDegree
  have hlen0 : rs.length = 5 + 1 := by simpa using hlen
  rcases List.length_eq_succ_iff.mp hlen0 with ⟨a, rs1, hcons0, hlen1⟩
  rw [← hcons0] at hrs_sorted hrs_eq
  have hlen1' : rs1.length = 4 + 1 := by simpa using hlen1
  rcases List.length_eq_succ_iff.mp hlen1' with ⟨b, rs2, hcons1, hlen2⟩
  rw [← hcons1] at hrs_sorted hrs_eq
  have hlen2' : rs2.length = 3 + 1 := by simpa using hlen2
  rcases List.length_eq_succ_iff.mp hlen2' with ⟨c, rs3, hcons2, hlen3⟩
  rw [← hcons2] at hrs_sorted hrs_eq
  have hlen3' : rs3.length = 2 + 1 := by simpa using hlen3
  rcases List.length_eq_succ_iff.mp hlen3' with ⟨d, rs4, hcons3, hlen4⟩
  rw [← hcons3] at hrs_sorted hrs_eq
  have hlen4' : rs4.length = 1 + 1 := by simpa using hlen4
  rcases List.length_eq_succ_iff.mp hlen4' with ⟨e, rs5, hcons4, hlen5⟩
  rw [← hcons4] at hrs_sorted hrs_eq
  have hlen5' : rs5.length = 0 + 1 := by simpa using hlen5
  rcases List.length_eq_succ_iff.mp hlen5' with ⟨r, rs6, hcons5, hlen6⟩
  rw [← hcons5] at hrs_sorted hrs_eq
  have hrs6_nil : rs6 = [] := List.length_eq_zero_iff.mp hlen6
  rw [hrs6_nil] at hrs_sorted hrs_eq
  refine ⟨a, b, c, d, e, r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hrs_eq.symm
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all

/-- Modified Narayana polynomials are nonzero and split over the reals. -/
theorem modifiedNarayanaPolynomial_ne_zero_and_splits (n : ℕ) :
    modifiedNarayanaPolynomial n ≠ 0 ∧
      (modifiedNarayanaPolynomial n).Splits :=
  (modifiedNarayanaPolynomial_isPFPolynomial n).ne_zero_and_splits
    (modifiedNarayanaPolynomial_ne_zero n)

/-- All real roots of a modified Narayana polynomial are nonpositive. -/
theorem modifiedNarayanaPolynomial_roots_nonpos (n : ℕ) :
    ∀ r ∈ (modifiedNarayanaPolynomial n).roots, r ≤ 0 :=
  (modifiedNarayanaPolynomial_isPFPolynomial n).roots_nonpos

/-- Differ-by-one interlacing for a quadratic whose roots lie between the
ordered roots of a cubic. -/
theorem interlaces_of_quadratic_cubic_root_lists
    {g f : ℝ[X]} {a b c u v : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 2)
    (hf_roots : f.roots = (↑[a, b, c] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v) (hvc : v ≤ c) :
    Interlaces g f :=
  Interlaces.of_quadratic_cubic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc huv hau hub hbv hvc

/-- Differ-by-one interlacing for a cubic whose roots lie between the ordered
roots of a quartic. -/
theorem interlaces_of_cubic_quartic_root_lists
    {g f : ℝ[X]} {a b c d u v w : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 4) (hgdeg : g.natDegree = 3)
    (hf_roots : f.roots = (↑[a, b, c, d] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d) :
    Interlaces g f :=
  Interlaces.of_cubic_quartic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc hcd huv hvw hau hub hbv hvc hcw hwd

/-- Differ-by-one interlacing for a quartic whose roots lie between the
ordered roots of a quintic. -/
theorem interlaces_of_quartic_quintic_root_lists
    {g f : ℝ[X]} {a b c d e u v w z : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 5) (hgdeg : g.natDegree = 4)
    (hf_roots : f.roots = (↑[a, b, c, d, e] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w, z] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (huv : u ≤ v) (hvw : v ≤ w) (hwz : w ≤ z)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d)
    (hdz : d ≤ z) (hze : z ≤ e) :
    Interlaces g f :=
  Interlaces.of_quartic_quintic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc hcd hde huv hvw hwz hau hub hbv hvc hcw hwd hdz hze

/-- Differ-by-one interlacing for a quintic whose roots lie between the ordered
roots of a sextic. -/
theorem interlaces_of_quintic_sextic_root_lists
    {g f : ℝ[X]} {a b c d e r u v w z y : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfdeg : f.natDegree = 6) (hgdeg : g.natDegree = 5)
    (hf_roots : f.roots = (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hg_roots : g.roots = (↑[u, v, w, z, y] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (huv : u ≤ v) (hvw : v ≤ w) (hwz : w ≤ z) (hzy : z ≤ y)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hwd : w ≤ d)
    (hdz : d ≤ z) (hze : z ≤ e) (hey : e ≤ y) (hyr : y ≤ r) :
    Interlaces g f :=
  Interlaces.of_quintic_sextic_root_lists
    hf_ne hf_splits hg_ne hg_splits hfdeg hgdeg hf_roots hg_roots
    hab hbc hcd hde her huv hvw hwz hzy hau hub hbv hvc hcw hwd hdz hze hey hyr

/-- Exact factorization of the `G_6` auxiliary polynomial. -/
theorem auxiliaryG_six_factor :
    FiniteSkewBoard.auxiliaryG 6 =
      C (2 : ℝ) * (X + 1) *
        (C (3 : ℝ) * X ^ 4 + C (32 : ℝ) * X ^ 3 +
          C (73 : ℝ) * X ^ 2 + C (32 : ℝ) * X + C (3 : ℝ)) := by
  rw [FiniteSkewBoard.auxiliaryG_six]
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC32 : (C (32 : ℝ) : ℝ[X]) = 32 := Polynomial.C_eq_natCast (R := ℝ) 32
  have hC70 : (C (70 : ℝ) : ℝ[X]) = 70 := Polynomial.C_eq_natCast (R := ℝ) 70
  have hC73 : (C (73 : ℝ) : ℝ[X]) = 73 := Polynomial.C_eq_natCast (R := ℝ) 73
  have hC210 : (C (210 : ℝ) : ℝ[X]) = 210 :=
    Polynomial.C_eq_natCast (R := ℝ) 210
  rw [hC2, hC3, hC6, hC32, hC70, hC73, hC210]
  ring

/-- Scaled real-quadratic factorization of the quartic factor in `G_6`. -/
theorem auxiliaryG_six_quartic_scaled_factor :
    C (3 : ℝ) *
        (C (3 : ℝ) * X ^ 4 + C (32 : ℝ) * X ^ 3 +
          C (73 : ℝ) * X ^ 2 + C (32 : ℝ) * X + C (3 : ℝ)) =
      (C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) + Real.sqrt (55 : ℝ)) * X +
          C (3 : ℝ)) *
        (C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) - Real.sqrt (55 : ℝ)) * X +
          C (3 : ℝ)) := by
  have hs_sq' : Real.sqrt (55 : ℝ) ^ 2 = (55 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hCsq : (C (Real.sqrt (55 : ℝ)) : ℝ[X]) ^ 2 = C (55 : ℝ) := by
    rw [← map_pow, hs_sq']
  have hCplus :
      (C ((16 : ℝ) + Real.sqrt (55 : ℝ)) : ℝ[X]) =
        C (16 : ℝ) + C (Real.sqrt (55 : ℝ)) := by
    rw [map_add]
  have hCminus :
      (C ((16 : ℝ) - Real.sqrt (55 : ℝ)) : ℝ[X]) =
        C (16 : ℝ) - C (Real.sqrt (55 : ℝ)) := by
    rw [map_sub]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC16 : (C (16 : ℝ) : ℝ[X]) = 16 := Polynomial.C_eq_natCast (R := ℝ) 16
  have hC32 : (C (32 : ℝ) : ℝ[X]) = 32 := Polynomial.C_eq_natCast (R := ℝ) 32
  have hC55 : (C (55 : ℝ) : ℝ[X]) = 55 := Polynomial.C_eq_natCast (R := ℝ) 55
  have hC73 : (C (73 : ℝ) : ℝ[X]) = 73 := Polynomial.C_eq_natCast (R := ℝ) 73
  rw [hCplus, hCminus]
  rw [hC3, hC16, hC32, hC73]
  ring_nf
  rw [hCsq, hC55]
  ring_nf

/-- Root multiset of the `G_6` auxiliary polynomial. -/
theorem auxiliaryG_six_roots :
    let s : ℝ := Real.sqrt (55 : ℝ)
    let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
    let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
    let u : ℝ := (-s + -16 - α) / 6
    let v : ℝ := (s - 16 - β) / 6
    let w : ℝ := -(1 : ℝ)
    let z : ℝ := (s - 16 + β) / 6
    let y : ℝ := (-s + -16 + α) / 6
    (FiniteSkewBoard.auxiliaryG 6).roots = (↑[u, v, w, z, y] : Multiset ℝ) := by
  dsimp
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  let u : ℝ := (-s + -16 - α) / 6
  let v : ℝ := (s - 16 - β) / 6
  let w : ℝ := -(1 : ℝ)
  let z : ℝ := (s - 16 + β) / 6
  let y : ℝ := (-s + -16 + α) / 6
  let quartic : ℝ[X] :=
    C (3 : ℝ) * X ^ 4 + C (32 : ℝ) * X ^ 3 +
      C (73 : ℝ) * X ^ 2 + C (32 : ℝ) * X + C (3 : ℝ)
  let qPlus : ℝ[X] :=
    C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) + s) * X + C (3 : ℝ)
  let qMinus : ℝ[X] :=
    C (3 : ℝ) * X ^ 2 + C ((16 : ℝ) - s) * X + C (3 : ℝ)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hqPlus_deg : qPlus.natDegree = 2 := by
    dsimp [qPlus]
    compute_degree!
  have hqPlus_ne : qPlus ≠ 0 := by
    intro hzero
    rw [hzero] at hqPlus_deg
    norm_num at hqPlus_deg
  have hqMinus_deg : qMinus.natDegree = 2 := by
    dsimp [qMinus]
    compute_degree!
  have hqMinus_ne : qMinus ≠ 0 := by
    intro hzero
    rw [hzero] at hqMinus_deg
    norm_num at hqMinus_deg
  have hquartic_deg : quartic.natDegree = 4 := by
    dsimp [quartic]
    compute_degree!
  have hquartic_ne : quartic ≠ 0 := by
    intro hzero
    rw [hzero] at hquartic_deg
    norm_num at hquartic_deg
  have hquartic_scaled : C (3 : ℝ) * quartic = qPlus * qMinus := by
    dsimp [quartic, qPlus, qMinus, s]
    exact auxiliaryG_six_quartic_scaled_factor
  have hdiscPlus : ((16 : ℝ) + s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) =
      (275 : ℝ) + 32 * s := by
    nlinarith only [hs_sq]
  have hdiscMinus : ((16 : ℝ) - s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) =
      (275 : ℝ) - 32 * s := by
    nlinarith only [hs_sq]
  have hdiscPlus_nonneg :
      0 ≤ ((16 : ℝ) + s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) := by
    rw [hdiscPlus]
    positivity
  have hdiscMinus_nonneg :
      0 ≤ ((16 : ℝ) - s) ^ 2 - 4 * (3 : ℝ) * (3 : ℝ) := by
    rw [hdiscMinus]
    nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hquartic_roots : quartic.roots = (↑[u, y, v, z] : Multiset ℝ) := by
    rw [← roots_C_mul quartic (show (3 : ℝ) ≠ 0 by norm_num)]
    rw [hquartic_scaled]
    rw [roots_mul (mul_ne_zero hqPlus_ne hqMinus_ne)]
    rw [roots_quadratic_posLead (a := (3 : ℝ)) (b := ((16 : ℝ) + s))
      (c := (3 : ℝ)) (by norm_num) hdiscPlus_nonneg]
    rw [roots_quadratic_posLead (a := (3 : ℝ)) (b := ((16 : ℝ) - s))
      (c := (3 : ℝ)) (by norm_num) hdiscMinus_nonneg]
    rw [hdiscPlus, hdiscMinus]
    dsimp [u, y, v, z, α, β]
    norm_num
    change (↑[v, u, y, z] : Multiset ℝ) = ↑[u, y, v, z]
    rw [Multiset.coe_eq_coe]
    exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ _))
  have hGfactor :
      FiniteSkewBoard.auxiliaryG 6 = C (2 : ℝ) * (X - C w) * quartic := by
    rw [auxiliaryG_six_factor]
    dsimp [quartic, w]
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hCneg1]
    ring_nf
  rw [hGfactor]
  rw [roots_mul
    (mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
      (X_sub_C_ne_zero w)) hquartic_ne)]
  rw [roots_mul (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
    (X_sub_C_ne_zero w))]
  rw [roots_C, roots_X_sub_C, hquartic_roots]
  dsimp [w]
  change (↑[-1, u, y, v, z] : Multiset ℝ) = ↑[u, v, -1, z, y]
  rw [Multiset.coe_eq_coe]
  exact List.Perm.trans (List.Perm.swap _ _ _)
    (List.Perm.cons _ <|
      List.Perm.trans
        (List.Perm.cons _ (List.Perm.swap _ _ _))
        (List.Perm.trans (List.Perm.swap _ _ _)
          (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))))

/-- The displayed roots in `auxiliaryG_six_roots` are ordered increasingly. -/
theorem auxiliaryG_six_root_order :
    let s : ℝ := Real.sqrt (55 : ℝ)
    let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
    let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
    let u : ℝ := (-s + -16 - α) / 6
    let v : ℝ := (s - 16 - β) / 6
    let w : ℝ := -(1 : ℝ)
    let z : ℝ := (s - 16 + β) / 6
    let y : ℝ := (-s + -16 + α) / 6
    u ≤ v ∧ v ≤ w ∧ w ≤ z ∧ z ≤ y := by
  dsimp
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  let u : ℝ := (-s + -16 - α) / 6
  let v : ℝ := (s - 16 - β) / 6
  let w : ℝ := -(1 : ℝ)
  let z : ℝ := (s - 16 + β) / 6
  let y : ℝ := (-s + -16 + α) / 6
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_ge7 : (7 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le8 : s ≤ (8 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by
    nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hβ_le8 : β ≤ (8 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [hs_ge7]
  have hβ_le_2sα : β ≤ 2 * s + α := by
    nlinarith [hβ_nonneg, hs_nonneg, hα_nonneg]
  have hten_minus_s_leβ : (10 : ℝ) - s ≤ β := by
    dsimp [β]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_sq, hs_le8]
  have h2sβ_leα : 2 * s + β ≤ α := by
    have hmul : 4 * s * β ≤ 4 * s * 8 := by
      exact mul_le_mul_of_nonneg_left hβ_le8 (by positivity)
    have hsq_le : (2 * s + β) ^ 2 ≤ α ^ 2 := by
      nlinarith [hs_sq, hβ_sq, hα_sq, hmul, hs_ge7]
    nlinarith [sq_nonneg (α - (2 * s + β)), hsq_le, hα_nonneg, hs_nonneg,
      hβ_nonneg]
  constructor
  · nlinarith [hβ_le_2sα]
  constructor
  · nlinarith [hs_le8, hβ_nonneg]
  constructor
  · nlinarith [hten_minus_s_leβ]
  · nlinarith [h2sβ_leα]

/-- The first displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root0 : ℝ :=
  (-Real.sqrt (55 : ℝ) + -16 -
    Real.sqrt ((275 : ℝ) + 32 * Real.sqrt (55 : ℝ))) / 6

/-- The second displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root1 : ℝ :=
  (Real.sqrt (55 : ℝ) - 16 -
    Real.sqrt ((275 : ℝ) - 32 * Real.sqrt (55 : ℝ))) / 6

/-- The middle displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root2 : ℝ :=
  -(1 : ℝ)

/-- The fourth displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root3 : ℝ :=
  (Real.sqrt (55 : ℝ) - 16 +
    Real.sqrt ((275 : ℝ) - 32 * Real.sqrt (55 : ℝ))) / 6

/-- The fifth displayed root of the `G_6` auxiliary polynomial. -/
def auxiliaryG_six_root4 : ℝ :=
  (-Real.sqrt (55 : ℝ) + -16 +
    Real.sqrt ((275 : ℝ) + 32 * Real.sqrt (55 : ℝ))) / 6

/-- Root multiset of `G_6`, stated using named roots. -/
theorem auxiliaryG_six_roots_named :
    (FiniteSkewBoard.auxiliaryG 6).roots =
      (↑[auxiliaryG_six_root0, auxiliaryG_six_root1, auxiliaryG_six_root2,
        auxiliaryG_six_root3, auxiliaryG_six_root4] : Multiset ℝ) := by
  simpa [auxiliaryG_six_root0, auxiliaryG_six_root1, auxiliaryG_six_root2,
    auxiliaryG_six_root3, auxiliaryG_six_root4] using auxiliaryG_six_roots

/-- The named roots of `G_6` are ordered increasingly. -/
theorem auxiliaryG_six_root_order_named :
    auxiliaryG_six_root0 ≤ auxiliaryG_six_root1 ∧
      auxiliaryG_six_root1 ≤ auxiliaryG_six_root2 ∧
        auxiliaryG_six_root2 ≤ auxiliaryG_six_root3 ∧
          auxiliaryG_six_root3 ≤ auxiliaryG_six_root4 := by
  simpa [auxiliaryG_six_root0, auxiliaryG_six_root1, auxiliaryG_six_root2,
    auxiliaryG_six_root3, auxiliaryG_six_root4] using auxiliaryG_six_root_order

/-- Degree of the `G_6` auxiliary polynomial. -/
theorem auxiliaryG_six_natDegree :
    (FiniteSkewBoard.auxiliaryG 6).natDegree = 5 := by
  rw [FiniteSkewBoard.auxiliaryG_six]
  compute_degree!

/-- The `G_6` auxiliary polynomial is nonzero. -/
theorem auxiliaryG_six_ne_zero : FiniteSkewBoard.auxiliaryG 6 ≠ 0 := by
  intro hzero
  have hdeg := auxiliaryG_six_natDegree
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The `G_6` auxiliary polynomial splits over `ℝ`. -/
theorem auxiliaryG_six_splits : (FiniteSkewBoard.auxiliaryG 6).Splits := by
  rw [Polynomial.splits_iff_card_roots]
  rw [auxiliaryG_six_roots]
  rw [auxiliaryG_six_natDegree]
  norm_num

/-- Shorthand for the modified Narayana polynomial `P_6`. -/
abbrev modifiedNarayanaPolynomialSix : ℝ[X] :=
  modifiedNarayanaPolynomial 6

/-- Evaluation of `P_6` at a root of the `+ sqrt 55` quadratic factor of
`G_6`. -/
theorem modifiedNarayanaPolynomial_six_eval_of_qPlus_root {s x : ℝ}
    (hs : s ^ 2 = (55 : ℝ))
    (hx : (3 : ℝ) * x ^ 2 + ((16 : ℝ) + s) * x + 3 = 0) :
    243 * modifiedNarayanaPolynomialSix.eval x =
      139370 * s * x + 18480 * s + 1015520 * x + 129855 := by
  rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one]
  have hs0 : s ^ 2 - 55 = 0 := by nlinarith [hs]
  linear_combination
    (81 * x ^ 4 + 1269 * x ^ 3 + 1656 * x ^ 2 + 4074 * x - 14879
      - 27 * s * x ^ 3 - 279 * s * x ^ 2 + 963 * s * x - 6215 * s
      + 9 * s ^ 2 * x ^ 2 + 45 * s ^ 2 * x - 570 * s ^ 2
      - 3 * s ^ 3 * x + s ^ 3 + s ^ 4) * hx
    - (s ^ 3 * x + 17 * s ^ 2 * x + 3 * s ^ 2 - 508 * s * x + 3 * s
      - 14265 * x - 1545) * hs0

/-- Evaluation of `P_6` at a root of the `- sqrt 55` quadratic factor of
`G_6`. -/
theorem modifiedNarayanaPolynomial_six_eval_of_qMinus_root {s x : ℝ}
    (hs : s ^ 2 = (55 : ℝ))
    (hx : (3 : ℝ) * x ^ 2 + ((16 : ℝ) - s) * x + 3 = 0) :
    243 * modifiedNarayanaPolynomialSix.eval x =
      -139370 * s * x - 18480 * s + 1015520 * x + 129855 := by
  rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_one]
  have hs0 : s ^ 2 - 55 = 0 := by nlinarith [hs]
  linear_combination
    (81 * x ^ 4 + 1269 * x ^ 3 + 1656 * x ^ 2 + 4074 * x - 14879
      + 27 * s * x ^ 3 + 279 * s * x ^ 2 - 963 * s * x + 6215 * s
      + 9 * s ^ 2 * x ^ 2 + 45 * s ^ 2 * x - 570 * s ^ 2
      + 3 * s ^ 3 * x - s ^ 3 + s ^ 4) * hx
    + (s ^ 3 * x - 17 * s ^ 2 * x - 3 * s ^ 2 - 508 * s * x + 3 * s
      + 14265 * x + 1545) * hs0

/-- The first named `G_6` root lies on the `+ sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root0_qPlus :
    (3 : ℝ) * auxiliaryG_six_root0 ^ 2 +
      ((16 : ℝ) + Real.sqrt (55 : ℝ)) * auxiliaryG_six_root0 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  dsimp [auxiliaryG_six_root0, s, α] at *
  nlinarith

/-- The second named `G_6` root lies on the `- sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root1_qMinus :
    (3 : ℝ) * auxiliaryG_six_root1 ^ 2 +
      ((16 : ℝ) - Real.sqrt (55 : ℝ)) * auxiliaryG_six_root1 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by
    nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  dsimp [auxiliaryG_six_root1, s, β] at *
  nlinarith

/-- The fourth named `G_6` root lies on the `- sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root3_qMinus :
    (3 : ℝ) * auxiliaryG_six_root3 ^ 2 +
      ((16 : ℝ) - Real.sqrt (55 : ℝ)) * auxiliaryG_six_root3 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by
    nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  dsimp [auxiliaryG_six_root3, s, β] at *
  nlinarith

/-- The fifth named `G_6` root lies on the `+ sqrt 55` quadratic factor. -/
theorem auxiliaryG_six_root4_qPlus :
    (3 : ℝ) * auxiliaryG_six_root4 ^ 2 +
      ((16 : ℝ) + Real.sqrt (55 : ℝ)) * auxiliaryG_six_root4 + 3 = 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  dsimp [auxiliaryG_six_root4, s, α] at *
  nlinarith

/-- The sign pattern of `P_6` at the named `G_6` roots. -/
def ModifiedNarayanaSixAuxiliaryGSignCertificate : Prop :=
  modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 < 0 ∧
    0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 ∧
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 < 0 ∧
        0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 ∧
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0

/-- `P_6` is negative at the first named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root0_neg :
    modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 < 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hroot0 :
      (3 : ℝ) * auxiliaryG_six_root0 ^ 2 +
        ((16 : ℝ) + s) * auxiliaryG_six_root0 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root0_qPlus
  have h0_num :
      139370 * s * auxiliaryG_six_root0 + 18480 * s +
          1015520 * auxiliaryG_six_root0 + 129855 < 0 := by
    dsimp [auxiliaryG_six_root0, s, α] at *
    nlinarith
  have h0_scaled :
      243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 < 0 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qPlus_root hs_sq hroot0]
  nlinarith

/-- `P_6` is positive at the second named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root1_pos :
    0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_ge37div5 : (37 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hroot1 :
      (3 : ℝ) * auxiliaryG_six_root1 ^ 2 +
        ((16 : ℝ) - s) * auxiliaryG_six_root1 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root1_qMinus
  have h1_num :
      0 < -139370 * s * auxiliaryG_six_root1 - 18480 * s +
        1015520 * auxiliaryG_six_root1 + 129855 := by
    dsimp [auxiliaryG_six_root1, s, β] at *
    nlinarith
  have h1_scaled :
      0 < 243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qMinus_root hs_sq hroot1]
  nlinarith

/-- `P_6` is negative at the middle named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root2_neg :
    modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 < 0 := by
  norm_num [modifiedNarayanaPolynomialSix, auxiliaryG_six_root2]

/-- `P_6` is positive at the fourth named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root3_pos :
    0 < modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let β : ℝ := Real.sqrt ((275 : ℝ) - 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_ge37div5 : (37 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le149div20 : s ≤ (149 / 20 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ_arg_nonneg : 0 ≤ (275 : ℝ) - 32 * s := by
    nlinarith [hs_sq, sq_nonneg (s - 8)]
  have hβ_sq : β ^ 2 = (275 : ℝ) - 32 * s := by
    dsimp [β]
    exact Real.sq_sqrt hβ_arg_nonneg
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hroot3 :
      (3 : ℝ) * auxiliaryG_six_root3 ^ 2 +
        ((16 : ℝ) - s) * auxiliaryG_six_root3 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root3_qMinus
  have h3_num :
      0 < -139370 * s * auxiliaryG_six_root3 - 18480 * s +
        1015520 * auxiliaryG_six_root3 + 129855 := by
    have hcoeff_nonneg : 0 ≤ (1267 : ℝ) * s - 9232 := by nlinarith
    have hA_nonneg : 0 ≤ ((1267 : ℝ) * s - 9232) * β :=
      mul_nonneg hcoeff_nonneg hβ_nonneg
    have hB_nonneg : 0 ≤ (28496 : ℝ) * s - 210314 := by nlinarith
    have hsq :
        (((1267 : ℝ) * s - 9232) * β) ^ 2 <
          ((28496 : ℝ) * s - 210314) ^ 2 := by
      have hdiff :
          0 < ((28496 : ℝ) * s - 210314) ^ 2 -
            (((1267 : ℝ) * s - 9232) * β) ^ 2 := by
        nlinarith [hs_sq, hβ_sq, hs_le149div20]
      nlinarith
    have hlt : ((1267 : ℝ) * s - 9232) * β < (28496 : ℝ) * s - 210314 := by
      have h_abs := (sq_lt_sq.mp hsq)
      simpa [abs_of_nonneg hA_nonneg, abs_of_nonneg hB_nonneg] using h_abs
    dsimp [auxiliaryG_six_root3, s, β] at *
    nlinarith
  have h3_scaled :
      0 < 243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qMinus_root hs_sq hroot3]
  nlinarith

/-- `P_6` is negative at the fifth named `G_6` root. -/
theorem modifiedNarayanaPolynomial_six_eval_root4_neg :
    modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0 := by
  let s : ℝ := Real.sqrt (55 : ℝ)
  let α : ℝ := Real.sqrt ((275 : ℝ) + 32 * s)
  have hs_sq : s ^ 2 = (55 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hα_sq : α ^ 2 = (275 : ℝ) + 32 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hroot4 :
      (3 : ℝ) * auxiliaryG_six_root4 ^ 2 +
        ((16 : ℝ) + s) * auxiliaryG_six_root4 + 3 = 0 := by
    dsimp [s]
    exact auxiliaryG_six_root4_qPlus
  have h4_num :
      139370 * s * auxiliaryG_six_root4 + 18480 * s +
          1015520 * auxiliaryG_six_root4 + 129855 < 0 := by
    have hA_nonneg : 0 ≤ ((9232 : ℝ) + 1267 * s) * α := by positivity
    have hB_nonneg : 0 ≤ (210314 : ℝ) + 28496 * s := by positivity
    have hsq :
        (((9232 : ℝ) + 1267 * s) * α) ^ 2 <
          ((210314 : ℝ) + 28496 * s) ^ 2 := by
      have hdiff :
          0 < ((210314 : ℝ) + 28496 * s) ^ 2 -
            (((9232 : ℝ) + 1267 * s) * α) ^ 2 := by
        nlinarith [hs_sq, hα_sq, hs_nonneg]
      nlinarith
    have hlt : ((9232 : ℝ) + 1267 * s) * α < (210314 : ℝ) + 28496 * s := by
      have h_abs := (sq_lt_sq.mp hsq)
      simpa [abs_of_nonneg hA_nonneg, abs_of_nonneg hB_nonneg] using h_abs
    dsimp [auxiliaryG_six_root4, s, α] at *
    nlinarith
  have h4_scaled :
      243 * modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0 := by
    rwa [modifiedNarayanaPolynomial_six_eval_of_qPlus_root hs_sq hroot4]
  nlinarith

/-- The concrete sign pattern of `P_6` at the five named `G_6` roots. -/
theorem modifiedNarayanaPolynomial_six_auxiliaryG_signCertificate :
    ModifiedNarayanaSixAuxiliaryGSignCertificate :=
  ⟨modifiedNarayanaPolynomial_six_eval_root0_neg,
    modifiedNarayanaPolynomial_six_eval_root1_pos,
    modifiedNarayanaPolynomial_six_eval_root2_neg,
    modifiedNarayanaPolynomial_six_eval_root3_pos,
    modifiedNarayanaPolynomial_six_eval_root4_neg⟩

/-- The roots of `P_6` are isolated across the five named `G_6` roots. -/
def ModifiedNarayanaSixAuxiliaryGRootIntervalCertificate : Prop :=
  ∃ x0 x1 x2 x3 x4 x5 : ℝ,
    modifiedNarayanaPolynomialSix.IsRoot x0 ∧
      x0 < auxiliaryG_six_root0 ∧
        modifiedNarayanaPolynomialSix.IsRoot x1 ∧
          auxiliaryG_six_root0 < x1 ∧ x1 < auxiliaryG_six_root1 ∧
            modifiedNarayanaPolynomialSix.IsRoot x2 ∧
              auxiliaryG_six_root1 < x2 ∧ x2 < auxiliaryG_six_root2 ∧
                modifiedNarayanaPolynomialSix.IsRoot x3 ∧
                  auxiliaryG_six_root2 < x3 ∧ x3 < auxiliaryG_six_root3 ∧
                    modifiedNarayanaPolynomialSix.IsRoot x4 ∧
                      auxiliaryG_six_root3 < x4 ∧ x4 < auxiliaryG_six_root4 ∧
                        modifiedNarayanaPolynomialSix.IsRoot x5 ∧
                          auxiliaryG_six_root4 < x5

/-- Sign alternation of `P_6` across the named `G_6` roots gives one `P_6`
root in each complementary interval. -/
theorem modifiedNarayanaPolynomial_six_rootIntervals_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    ModifiedNarayanaSixAuxiliaryGRootIntervalCertificate := by
  rcases hsign with ⟨h0, h1, h2, h3, h4⟩
  rcases auxiliaryG_six_root_order_named with ⟨h01, h12, h23, h34⟩
  have hP_pos : HasPosLeadingCoeff modifiedNarayanaPolynomialSix := by
    simpa [modifiedNarayanaPolynomialSix] using modifiedNarayanaPolynomial_posLeadingCoeff 6
  have hP_natdeg_pos : 0 < modifiedNarayanaPolynomialSix.natDegree := by
    rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six_natDegree]
    norm_num
  have hP_deg_pos : 0 < modifiedNarayanaPolynomialSix.degree :=
    natDegree_pos_iff_degree_pos.mp hP_natdeg_pos
  have hP_even : Even modifiedNarayanaPolynomialSix.natDegree := by
    rw [modifiedNarayanaPolynomialSix, modifiedNarayanaPolynomial_six_natDegree]
    norm_num
  have ht_bot : Tendsto (fun x => modifiedNarayanaPolynomialSix.eval x) atBot atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hP_pos hP_deg_pos hP_even
  have ht_top : Tendsto (fun x => modifiedNarayanaPolynomialSix.eval x) atTop atTop :=
    modifiedNarayanaPolynomialSix.tendsto_atTop_of_leadingCoeff_nonneg
      hP_deg_pos hP_pos.le
  obtain ⟨x0, hx0_le, hx0_root⟩ :=
    exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop h0 ht_bot
  have hx0_lt : x0 < auxiliaryG_six_root0 := by
    refine lt_of_le_of_ne hx0_le ?_
    intro hx0_eq
    have hx0_eval : modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 = 0 := by
      simpa [Polynomial.IsRoot.def, hx0_eq] using hx0_root
    linarith
  have h01_strict : auxiliaryG_six_root0 < auxiliaryG_six_root1 := by
    refine lt_of_le_of_ne h01 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 := by
      rw [h_eq]
    linarith
  have h12_strict : auxiliaryG_six_root1 < auxiliaryG_six_root2 := by
    refine lt_of_le_of_ne h12 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 := by
      rw [h_eq]
    linarith
  have h23_strict : auxiliaryG_six_root2 < auxiliaryG_six_root3 := by
    refine lt_of_le_of_ne h23 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 := by
      rw [h_eq]
    linarith
  have h34_strict : auxiliaryG_six_root3 < auxiliaryG_six_root4 := by
    refine lt_of_le_of_ne h34 ?_
    intro h_eq
    have heq_eval :
        modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 =
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 := by
      rw [h_eq]
    linarith
  have h01_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root0 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 < 0 := by
    nlinarith
  have h12_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root1 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 < 0 := by
    nlinarith
  have h23_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root2 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 < 0 := by
    nlinarith
  have h34_sign :
      modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root3 *
          modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 < 0 := by
    nlinarith
  obtain ⟨x1, hx1_left, hx1_right, hx1_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h01_strict h01_sign
  obtain ⟨x2, hx2_left, hx2_right, hx2_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h12_strict h12_sign
  obtain ⟨x3, hx3_left, hx3_right, hx3_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h23_strict h23_sign
  obtain ⟨x4, hx4_left, hx4_right, hx4_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg h34_strict h34_sign
  obtain ⟨x5, hx5_ge, hx5_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt h4) ht_top
  have hx5_lt : auxiliaryG_six_root4 < x5 := by
    refine lt_of_le_of_ne hx5_ge ?_
    intro hx5_eq
    have hx5_eval : modifiedNarayanaPolynomialSix.eval auxiliaryG_six_root4 = 0 := by
      simpa [Polynomial.IsRoot.def, hx5_eq] using hx5_root
    linarith
  exact ⟨x0, x1, x2, x3, x4, x5, hx0_root, hx0_lt, hx1_root, hx1_left,
    hx1_right, hx2_root, hx2_left, hx2_right, hx3_root, hx3_left, hx3_right,
    hx4_root, hx4_left, hx4_right, hx5_root, hx5_lt⟩

/-- Cross-root inequalities between an ordered `P_6` root list and the named
`G_6` roots. -/
def ModifiedNarayanaSixAuxiliaryGCrossInequalities
    (a b c d e r : ℝ) : Prop :=
  a ≤ auxiliaryG_six_root0 ∧ auxiliaryG_six_root0 ≤ b ∧
    b ≤ auxiliaryG_six_root1 ∧ auxiliaryG_six_root1 ≤ c ∧
      c ≤ auxiliaryG_six_root2 ∧ auxiliaryG_six_root2 ≤ d ∧
        d ≤ auxiliaryG_six_root3 ∧ auxiliaryG_six_root3 ≤ e ∧
          e ≤ auxiliaryG_six_root4 ∧ auxiliaryG_six_root4 ≤ r

/-- Six interval-isolated `P_6` roots determine the cross-root inequalities
against any sorted `P_6` root list. -/
theorem ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_rootIntervals
    {a b c d e r : ℝ}
    (hP_roots :
      modifiedNarayanaPolynomialSix.roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hintervals : ModifiedNarayanaSixAuxiliaryGRootIntervalCertificate) :
    ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r := by
  rcases hintervals with
    ⟨x0, x1, x2, x3, x4, x5, hx0_root, hx0_lt, hx1_root,
      hx01, hx1_lt, hx2_root, hx12, hx2_lt, hx3_root, hx23,
      hx3_lt, hx4_root, hx34, hx4_lt, hx5_root, hx45⟩
  have hx0x1 : x0 < x1 := lt_trans hx0_lt hx01
  have hx1x2 : x1 < x2 := lt_trans hx1_lt hx12
  have hx2x3 : x2 < x3 := lt_trans hx2_lt hx23
  have hx3x4 : x3 < x4 := lt_trans hx3_lt hx34
  have hx4x5 : x4 < x5 := lt_trans hx4_lt hx45
  have hxs_sorted_lt : ([x0, x1, x2, x3, x4, x5] : List ℝ).Pairwise (· < ·) := by
    simp [List.pairwise_cons]
    grind
  have hxs_sorted : ([x0, x1, x2, x3, x4, x5] : List ℝ).Pairwise (· ≤ ·) :=
    hxs_sorted_lt.imp (by intro _ _ h; exact le_of_lt h)
  have hxs_nodup_list : ([x0, x1, x2, x3, x4, x5] : List ℝ).Nodup :=
    hxs_sorted_lt.imp (by intro _ _ h; exact ne_of_lt h)
  have hxs_nodup : (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ).Nodup := by
    simpa using hxs_nodup_list
  have hP_ne : modifiedNarayanaPolynomialSix ≠ 0 := by
    simpa [modifiedNarayanaPolynomialSix] using modifiedNarayanaPolynomial_six_ne_zero
  have hx0_mem : x0 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx0_root
  have hx1_mem : x1 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx1_root
  have hx2_mem : x2 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx2_root
  have hx3_mem : x3 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx3_root
  have hx4_mem : x4 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx4_root
  have hx5_mem : x5 ∈ modifiedNarayanaPolynomialSix.roots :=
    (Polynomial.mem_roots hP_ne).mpr hx5_root
  have hxs_subset :
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) ⊆
        modifiedNarayanaPolynomialSix.roots := by
    intro y hy
    have hy' : y = x0 ∨ y = x1 ∨ y = x2 ∨ y = x3 ∨ y = x4 ∨ y = x5 := by
      simpa only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] using hy
    rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hx0_mem
    · exact hx1_mem
    · exact hx2_mem
    · exact hx3_mem
    · exact hx4_mem
    · exact hx5_mem
  have hxs_le :
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) ≤
        modifiedNarayanaPolynomialSix.roots :=
    (Multiset.le_iff_subset hxs_nodup).2 hxs_subset
  have hcard_le :
      modifiedNarayanaPolynomialSix.roots.card ≤
        (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ).card := by
    rw [hP_roots]
    norm_num
  have hxs_roots :
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) =
        modifiedNarayanaPolynomialSix.roots :=
    Multiset.eq_of_le_of_card_le hxs_le hcard_le
  have hperm : ([x0, x1, x2, x3, x4, x5] : List ℝ).Perm [a, b, c, d, e, r] := by
    apply Multiset.coe_eq_coe.mp
    calc
      (↑[x0, x1, x2, x3, x4, x5] : Multiset ℝ) =
          modifiedNarayanaPolynomialSix.roots := hxs_roots
      _ = (↑[a, b, c, d, e, r] : Multiset ℝ) := hP_roots
  have habs_sorted : ([a, b, c, d, e, r] : List ℝ).Pairwise (· ≤ ·) := by
    simp [hab, hbc, hcd, hde, her, hab.trans hbc, hbc.trans hcd,
      hcd.trans hde, hde.trans her, hab.trans (hbc.trans hcd),
      hbc.trans (hcd.trans hde), hcd.trans (hde.trans her),
      hab.trans (hbc.trans (hcd.trans hde)),
      hbc.trans (hcd.trans (hde.trans her)),
      hab.trans (hbc.trans (hcd.trans (hde.trans her)))]
  have hlist_eq : [x0, x1, x2, x3, x4, x5] = [a, b, c, d, e, r] :=
    List.Perm.eq_of_pairwise' hxs_sorted habs_sorted hperm
  have hcoords : x0 = a ∧ x1 = b ∧ x2 = c ∧ x3 = d ∧ x4 = e ∧ x5 = r := by
    simpa using hlist_eq
  rcases hcoords with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨le_of_lt hx0_lt, le_of_lt hx01, le_of_lt hx1_lt, le_of_lt hx12,
    le_of_lt hx2_lt, le_of_lt hx23, le_of_lt hx3_lt, le_of_lt hx34,
    le_of_lt hx4_lt, le_of_lt hx45⟩

/-- The `P_6`/`G_6` sign certificate gives the cross-root inequalities against
any sorted `P_6` root list. -/
theorem ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_eval_signs
    {a b c d e r : ℝ}
    (hP_roots :
      modifiedNarayanaPolynomialSix.roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r :=
  ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_rootIntervals
    hP_roots hab hbc hcd hde her
    (modifiedNarayanaPolynomial_six_rootIntervals_of_eval_signs hsign)

/-- Conditional `n = 6` Lemma 3.3 certificate, reducing the remaining work to
the `P_6` root list and cross inequalities. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_roots
    {a b c d e r : ℝ}
    (hP_roots :
      (modifiedNarayanaPolynomial 6).roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hau : a ≤ auxiliaryG_six_root0) (hub : auxiliaryG_six_root0 ≤ b)
    (hbv : b ≤ auxiliaryG_six_root1) (hvc : auxiliaryG_six_root1 ≤ c)
    (hcw : c ≤ auxiliaryG_six_root2) (hwd : auxiliaryG_six_root2 ≤ d)
    (hdz : d ≤ auxiliaryG_six_root3) (hze : auxiliaryG_six_root3 ≤ e)
    (hey : e ≤ auxiliaryG_six_root4) (hyr : auxiliaryG_six_root4 ≤ r) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  rcases auxiliaryG_six_root_order_named with ⟨huv, hvw, hwz, hzy⟩
  exact interlaces_of_quintic_sextic_root_lists
    modifiedNarayanaPolynomial_six_ne_zero modifiedNarayanaPolynomial_six_splits
    auxiliaryG_six_ne_zero auxiliaryG_six_splits
    modifiedNarayanaPolynomial_six_natDegree auxiliaryG_six_natDegree
    hP_roots auxiliaryG_six_roots_named hab hbc hcd hde her huv hvw hwz hzy hau
    hub hbv hvc hcw hwd hdz hze hey hyr

/-- Conditional `n = 6` Lemma 3.3 certificate, with the cross inequalities
bundled as a single predicate. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_root_crosses
    {a b c d e r : ℝ}
    (hP_roots :
      (modifiedNarayanaPolynomial 6).roots =
        (↑[a, b, c, d, e, r] : Multiset ℝ))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e)
    (her : e ≤ r)
    (hcross :
      ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  rcases hcross with ⟨hau, hub, hbv, hvc, hcw, hwd, hdz, hze, hey, hyr⟩
  exact lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_roots hP_roots
    hab hbc hcd hde her hau hub hbv hvc hcw hwd hdz hze hey hyr

/-- The `n = 6` Braun--Jal Lemma 3.3 interlacing follows from proving the
cross inequalities for any sorted `P_6` root list. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_crosses
    (hcross :
      ∀ {a b c d e r : ℝ},
        (modifiedNarayanaPolynomial 6).roots =
          (↑[a, b, c, d, e, r] : Multiset ℝ) →
        a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ r →
        ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  obtain ⟨a, b, c, d, e, r, hP_roots, hab, hbc, hcd, hde, her⟩ :=
    modifiedNarayanaPolynomial_six_exists_ordered_roots
  exact lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_root_crosses
    hP_roots hab hbc hcd hde her (hcross hP_roots hab hbc hcd hde her)

/-- The `n = 6` Braun--Jal Lemma 3.3 proper-position form follows from proving
the cross inequalities for any sorted `P_6` root list. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_of_crosses
    (hcross :
      ∀ {a b c d e r : ℝ},
        (modifiedNarayanaPolynomial 6).roots =
          (↑[a, b, c, d, e, r] : Multiset ℝ) →
        a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ r →
        ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r) :
    Prec (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  exact (lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_crosses hcross).toPrec

/-- The `n = 6` Braun--Jal Lemma 3.3 interlacing follows from the
`P_6`/`G_6` sign certificate. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) := by
  apply lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_crosses
  intro a b c d e r hP_roots hab hbc hcd hde her
  exact ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_eval_signs
    (by simpa [modifiedNarayanaPolynomialSix] using hP_roots)
    hab hbc hcd hde her hsign

/-- The `n = 6` Braun--Jal Lemma 3.3 proper-position form follows from the
`P_6`/`G_6` sign certificate. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate) :
    Prec (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) :=
  (lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_eval_signs hsign).toPrec

/-- The checked `n = 6` Braun--Jal Lemma 3.3 interlacing case. -/
theorem lemma33AuxiliaryGInterlaces_modified_six_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) :=
  lemma33AuxiliaryGInterlaces_modified_six_interlaces_of_eval_signs
    modifiedNarayanaPolynomial_six_auxiliaryG_signCertificate

/-- The checked `n = 6` Braun--Jal Lemma 3.3 proper-position case. -/
theorem lemma33AuxiliaryGInterlaces_modified_six :
    Prec (FiniteSkewBoard.auxiliaryG 6) (modifiedNarayanaPolynomial 6) :=
  lemma33AuxiliaryGInterlaces_modified_six_interlaces.toPrec

/-- The `n = 3` case of Braun--Jal Lemma 3.3, in the stricter differ-by-one
interlacing form. -/
theorem lemma33AuxiliaryGInterlaces_modified_three_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 3) (modifiedNarayanaPolynomial 3) := by
  let a : ℝ := (-(5 : ℝ) - Real.sqrt (21 : ℝ)) / 2
  let b : ℝ := -(1 : ℝ)
  let c : ℝ := (-(5 : ℝ) + Real.sqrt (21 : ℝ)) / 2
  let u : ℝ := (-(8 : ℝ) - Real.sqrt (28 : ℝ)) / 6
  let v : ℝ := (-(8 : ℝ) + Real.sqrt (28 : ℝ)) / 6
  have hGform :
      FiniteSkewBoard.auxiliaryG 3 =
        C (3 : ℝ) * X ^ 2 + C (8 : ℝ) * X + C (3 : ℝ) := by
    rw [FiniteSkewBoard.auxiliaryG_three]
    have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
    have hC8 : (C (8 : ℝ) : ℝ[X]) = 8 := Polynomial.C_eq_natCast (R := ℝ) 8
    rw [hC3, hC8]
    ring_nf
  have hGdeg : (FiniteSkewBoard.auxiliaryG 3).natDegree = 2 := by
    rw [FiniteSkewBoard.auxiliaryG_three]
    compute_degree!
  have hG_ne : FiniteSkewBoard.auxiliaryG 3 ≠ 0 := by
    intro hzero
    rw [hzero] at hGdeg
    norm_num at hGdeg
  have hG_splits : (FiniteSkewBoard.auxiliaryG 3).Splits := by
    rw [hGform]
    exact quadraticPoly_splits_of_discrim_nonneg (by norm_num) (by norm_num [discrim])
  have hG_roots : (FiniteSkewBoard.auxiliaryG 3).roots = (↑[u, v] : Multiset ℝ) := by
    rw [hGform]
    rw [roots_quadratic_posLead (a := (3 : ℝ)) (b := (8 : ℝ))
      (c := (3 : ℝ)) (by norm_num) (by norm_num)]
    dsimp [u, v]
    norm_num
    rfl
  have hPfactor :
      modifiedNarayanaPolynomial 3 =
        (X - C (-(1 : ℝ))) *
          (C (1 : ℝ) * X ^ 2 + C (5 : ℝ) * X + C (1 : ℝ)) := by
    rw [modifiedNarayanaPolynomial_three]
    have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
    have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hC5, hC6, hCneg1]
    norm_num
    ring_nf
  have hquad_deg :
      (C (1 : ℝ) * X ^ 2 + C (5 : ℝ) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquad_ne :
      (C (1 : ℝ) * X ^ 2 + C (5 : ℝ) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquad_deg
    norm_num at hquad_deg
  have hP_roots :
      (modifiedNarayanaPolynomial 3).roots = (↑[a, b, c] : Multiset ℝ) := by
    rw [hPfactor]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero (-(1 : ℝ))) hquad_ne)]
    rw [roots_X_sub_C]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := (5 : ℝ))
      (c := (1 : ℝ)) (by norm_num) (by norm_num)]
    dsimp [a, b, c]
    norm_num
    rw [Multiset.cons_swap]
    rfl
  have hP_ne : modifiedNarayanaPolynomial 3 ≠ 0 := modifiedNarayanaPolynomial_ne_zero 3
  have hP_splits : (modifiedNarayanaPolynomial 3).Splits :=
    modifiedNarayanaPolynomial_splits 3
  have hPdeg : (modifiedNarayanaPolynomial 3).natDegree = 3 := by
    rw [modifiedNarayanaPolynomial_natDegree]
  have h21 : Real.sqrt (21 : ℝ) ^ 2 = (21 : ℝ) := Real.sq_sqrt (by norm_num)
  have h28 : Real.sqrt (28 : ℝ) ^ 2 = (28 : ℝ) := Real.sq_sqrt (by norm_num)
  have h21nonneg : 0 ≤ Real.sqrt (21 : ℝ) := Real.sqrt_nonneg _
  have h28nonneg : 0 ≤ Real.sqrt (28 : ℝ) := Real.sqrt_nonneg _
  have h3le21 : (3 : ℝ) ≤ Real.sqrt (21 : ℝ) := by nlinarith
  have h2le28 : (2 : ℝ) ≤ Real.sqrt (28 : ℝ) := by nlinarith
  have hab : a ≤ b := by
    dsimp [a, b]
    nlinarith
  have hbc : b ≤ c := by
    dsimp [b, c]
    nlinarith
  have huv : u ≤ v := by
    dsimp [u, v]
    nlinarith
  have hau : a ≤ u := by
    dsimp [a, u]
    nlinarith
  have hub : u ≤ b := by
    dsimp [u, b]
    nlinarith
  have hbv : b ≤ v := by
    dsimp [b, v]
    nlinarith
  have hvc : v ≤ c := by
    dsimp [v, c]
    nlinarith [sq_nonneg (3 * Real.sqrt (21 : ℝ) - (7 + Real.sqrt (28 : ℝ)))]
  exact interlaces_of_quadratic_cubic_root_lists hP_ne hP_splits hG_ne hG_splits
    hPdeg hGdeg hP_roots hG_roots hab hbc huv hau hub hbv hvc

/-- The `n = 3` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_three :
    Prec (FiniteSkewBoard.auxiliaryG 3) (modifiedNarayanaPolynomial 3) := by
  exact lemma33AuxiliaryGInterlaces_modified_three_interlaces.toPrec

/-- The checked initial cases `n = 1, 2, 3` of Braun--Jal Lemma 3.3, for the
concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_three
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₃ : n ≤ 3) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three

/-- The `n = 4` case of Braun--Jal Lemma 3.3, in the stricter differ-by-one
interlacing form. -/
theorem lemma33AuxiliaryGInterlaces_modified_four_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 4) (modifiedNarayanaPolynomial 4) := by
  let s : ℝ := Real.sqrt (7 : ℝ)
  let α : ℝ := Real.sqrt ((28 : ℝ) + 10 * s)
  let β : ℝ := Real.sqrt ((28 : ℝ) - 10 * s)
  let γ : ℝ := Real.sqrt (12 : ℝ)
  let a : ℝ := (-(5 : ℝ) - s - α) / 2
  let b : ℝ := (-(5 : ℝ) + s - β) / 2
  let c : ℝ := (-(5 : ℝ) + s + β) / 2
  let d : ℝ := (-(5 : ℝ) - s + α) / 2
  let u : ℝ := (-(4 : ℝ) - γ) / 2
  let v : ℝ := -(1 : ℝ)
  let w : ℝ := (-(4 : ℝ) + γ) / 2
  have hGfactor :
      FiniteSkewBoard.auxiliaryG 4 =
        C (4 : ℝ) * (X - C v) *
          (C (1 : ℝ) * X ^ 2 + C (4 : ℝ) * X + C (1 : ℝ)) := by
    rw [FiniteSkewBoard.auxiliaryG_four]
    dsimp [v]
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
    have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 :=
      Polynomial.C_eq_natCast (R := ℝ) 20
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hC1, hC4, hC20, hCneg1]
    ring_nf
  have hGdeg : (FiniteSkewBoard.auxiliaryG 4).natDegree = 3 := by
    rw [FiniteSkewBoard.auxiliaryG_four]
    compute_degree!
  have hG_ne : FiniteSkewBoard.auxiliaryG 4 ≠ 0 := by
    intro hzero
    rw [hzero] at hGdeg
    norm_num at hGdeg
  have hquadG_deg :
      (C (1 : ℝ) * X ^ 2 + C (4 : ℝ) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadG_ne :
      (C (1 : ℝ) * X ^ 2 + C (4 : ℝ) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadG_deg
    norm_num at hquadG_deg
  have hXv_ne : X - C v ≠ 0 := X_sub_C_ne_zero v
  have hG_splits : (FiniteSkewBoard.auxiliaryG 4).Splits := by
    rw [hGfactor]
    exact
      ((Polynomial.Splits.C (4 : ℝ)).mul (Polynomial.Splits.X_sub_C v)).mul
        (quadraticPoly_splits_of_discrim_nonneg (by norm_num)
          (by norm_num [discrim]))
  have hG_roots :
      (FiniteSkewBoard.auxiliaryG 4).roots = (↑[u, v, w] : Multiset ℝ) := by
    rw [hGfactor]
    rw [roots_mul
      (mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) hXv_ne)
        hquadG_ne)]
    rw [roots_mul (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) hXv_ne)]
    rw [roots_C, roots_X_sub_C]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := (4 : ℝ))
      (c := (1 : ℝ)) (by norm_num) (by norm_num)]
    dsimp [u, v, w, γ]
    norm_num
    rfl
  have hPfactor :
      modifiedNarayanaPolynomial 4 =
        (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) + s) * X + C (1 : ℝ)) *
          (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) - s) * X + C (1 : ℝ)) := by
    rw [modifiedNarayanaPolynomial_four]
    dsimp [s]
    have hs_sq' : Real.sqrt (7 : ℝ) ^ 2 = (7 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hCsq : (C (Real.sqrt (7 : ℝ)) : ℝ[X]) ^ 2 = C (7 : ℝ) := by
      rw [← map_pow, hs_sq']
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
    have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
    have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 :=
      Polynomial.C_eq_natCast (R := ℝ) 10
    have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 :=
      Polynomial.C_eq_natCast (R := ℝ) 20
    rw [hC1, hC10, hC20]
    norm_num
    ring_nf
    rw [hCsq, hC5, hC7]
    ring_nf
  have hquadA_deg :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) + s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadA_ne :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) + s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadA_deg
    norm_num at hquadA_deg
  have hquadB_deg :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) - s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadB_ne :
      (C (1 : ℝ) * X ^ 2 + C ((5 : ℝ) - s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadB_deg
    norm_num at hquadB_deg
  have hs_sq : s ^ 2 = (7 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hdiscA :
      ((5 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) = (28 : ℝ) + 10 * s := by
    nlinarith [hs_sq]
  have hdiscB :
      ((5 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) = (28 : ℝ) - 10 * s := by
    nlinarith [hs_sq]
  have hdiscA_nonneg :
      0 ≤ ((5 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
    rw [hdiscA]
    positivity
  have hdiscB_nonneg :
      0 ≤ ((5 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
    rw [hdiscB]
    apply sub_nonneg.mpr
    nlinarith [sq_nonneg (s - 5)]
  have hP_roots :
      (modifiedNarayanaPolynomial 4).roots = (↑[a, b, c, d] : Multiset ℝ) := by
    rw [hPfactor]
    rw [roots_mul (mul_ne_zero hquadA_ne hquadB_ne)]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((5 : ℝ) + s))
      (c := (1 : ℝ)) (by norm_num) hdiscA_nonneg]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((5 : ℝ) - s))
      (c := (1 : ℝ)) (by norm_num) hdiscB_nonneg]
    rw [hdiscA, hdiscB]
    norm_num
    dsimp [a, b, c, d, α, β]
    ring_nf
    change
      (↑[-5 / 2 + s * (1 / 2) + Real.sqrt (28 - s * 10) * (-1 / 2),
        -5 / 2 + s * (-1 / 2) + Real.sqrt (28 + s * 10) * (-1 / 2),
        -5 / 2 + s * (-1 / 2) + Real.sqrt (28 + s * 10) * (1 / 2),
        -5 / 2 + s * (1 / 2) + Real.sqrt (28 - s * 10) * (1 / 2)] :
        Multiset ℝ) = _
    rw [Multiset.coe_eq_coe]
    exact
      List.Perm.trans (List.Perm.swap _ _ _)
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))
  have hP_ne : modifiedNarayanaPolynomial 4 ≠ 0 := modifiedNarayanaPolynomial_ne_zero 4
  have hP_splits : (modifiedNarayanaPolynomial 4).Splits :=
    modifiedNarayanaPolynomial_splits 4
  have hPdeg : (modifiedNarayanaPolynomial 4).natDegree = 4 := by
    rw [modifiedNarayanaPolynomial_natDegree]
  have hα_sq : α ^ 2 = (28 : ℝ) + 10 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hβ_sq : β ^ 2 = (28 : ℝ) - 10 * s := by
    dsimp [β]
    apply Real.sq_sqrt
    nlinarith [sq_nonneg (s - 5)]
  have hγ_sq : γ ^ 2 = (12 : ℝ) := by
    dsimp [γ]
    exact Real.sq_sqrt (by norm_num)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    exact Real.sqrt_nonneg _
  have hs_ge2 : (2 : ℝ) ≤ s := by
    dsimp [s]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hs_ge5div2 : (5 / 2 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le3 : s ≤ (3 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs_le8div3 : s ≤ (8 / 3 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hβ_le2 : β ≤ (2 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [hs_ge5div2]
  have hβ_ge1 : (1 : ℝ) ≤ β := by
    dsimp [β]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_le8div3]
  have hγ_ge1 : (1 : ℝ) ≤ γ := by
    dsimp [γ]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hγ_ge2 : (2 : ℝ) ≤ γ := by
    dsimp [γ]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hγ_le4 : γ ≤ (4 : ℝ) := by
    dsimp [γ]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hα_ge1 : (1 : ℝ) ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_nonneg]
  have h2s2_leα : 2 * s + 2 ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs_sq, hs_ge2]
  have hsumβ_leα : 2 * s + β ≤ α := by
    linarith
  have hsumβγ_le : s + β - 1 ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    have hs1_nonneg : 0 ≤ s - 1 := by linarith
    have hmul : β * (s - 1) ≤ 2 * (s - 1) :=
      mul_le_mul_of_nonneg_right hβ_le2 hs1_nonneg
    nlinarith [hs_sq, hβ_sq, hmul, hs_ge5div2]
  have hsumγα_le : γ + s + 1 ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    have hsp1_nonneg : 0 ≤ s + 1 := by positivity
    have hmul : γ * (s + 1) ≤ 4 * (s + 1) :=
      mul_le_mul_of_nonneg_right hγ_le4 hsp1_nonneg
    nlinarith [hs_sq, hγ_sq, hmul]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hbc : b ≤ c := by
    dsimp [b, c]
    linarith
  have hcd : c ≤ d := by
    dsimp [c, d]
    linarith
  have huv : u ≤ v := by
    dsimp [u, v]
    linarith
  have hvw : v ≤ w := by
    dsimp [v, w]
    linarith
  have hau : a ≤ u := by
    dsimp [a, u]
    linarith
  have hub : u ≤ b := by
    dsimp [u, b]
    linarith
  have hbv : b ≤ v := by
    dsimp [b, v]
    linarith
  have hvc : v ≤ c := by
    dsimp [v, c]
    linarith
  have hcw : c ≤ w := by
    dsimp [c, w]
    linarith
  have hwd : w ≤ d := by
    dsimp [w, d]
    linarith
  exact interlaces_of_cubic_quartic_root_lists hP_ne hP_splits hG_ne hG_splits
    hPdeg hGdeg hP_roots hG_roots hab hbc hcd huv hvw hau hub hbv hvc hcw hwd

/-- The `n = 4` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_four :
    Prec (FiniteSkewBoard.auxiliaryG 4) (modifiedNarayanaPolynomial 4) := by
  exact lemma33AuxiliaryGInterlaces_modified_four_interlaces.toPrec

/-- The checked initial cases `n = 1, 2, 3, 4` of Braun--Jal Lemma 3.3, for the
concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_four
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₄ : n ≤ 4) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three
  · exact lemma33AuxiliaryGInterlaces_modified_four

/-- The `n = 5` case of Braun--Jal Lemma 3.3, in the stricter differ-by-one
interlacing form. -/
theorem lemma33AuxiliaryGInterlaces_modified_five_interlaces :
    Interlaces (FiniteSkewBoard.auxiliaryG 5) (modifiedNarayanaPolynomial 5) := by
  let s : ℝ := Real.sqrt (3 : ℝ)
  let t : ℝ := Real.sqrt (15 : ℝ)
  let α : ℝ := Real.sqrt ((15 : ℝ) + 8 * s)
  let β : ℝ := Real.sqrt ((15 : ℝ) - 8 * s)
  let γ : ℝ := Real.sqrt ((60 : ℝ) + 14 * t)
  let δ : ℝ := Real.sqrt ((60 : ℝ) - 14 * t)
  let a : ℝ := (-(7 : ℝ) - t - γ) / 2
  let b : ℝ := (-(7 : ℝ) + t - δ) / 2
  let c : ℝ := -(1 : ℝ)
  let d : ℝ := (-(7 : ℝ) + t + δ) / 2
  let e : ℝ := (-(7 : ℝ) - t + γ) / 2
  let u : ℝ := (-(4 : ℝ) - s - α) / 2
  let v : ℝ := (-(4 : ℝ) + s - β) / 2
  let w : ℝ := (-(4 : ℝ) + s + β) / 2
  let z : ℝ := (-(4 : ℝ) - s + α) / 2
  have hGfactor :
      FiniteSkewBoard.auxiliaryG 5 =
        C (5 : ℝ) *
          ((C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) + s) * X + C (1 : ℝ)) *
            (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) - s) * X + C (1 : ℝ))) := by
    rw [FiniteSkewBoard.auxiliaryG_five]
    dsimp [s]
    have hs_sq' : Real.sqrt (3 : ℝ) ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hCsq : (C (Real.sqrt (3 : ℝ)) : ℝ[X]) ^ 2 = C (3 : ℝ) := by
      rw [← map_pow, hs_sq']
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
    have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
    have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
    have hC40 : (C (40 : ℝ) : ℝ[X]) = 40 :=
      Polynomial.C_eq_natCast (R := ℝ) 40
    have hC75 : (C (75 : ℝ) : ℝ[X]) = 75 :=
      Polynomial.C_eq_natCast (R := ℝ) 75
    rw [hC1, hC5, hC40, hC75]
    norm_num
    ring_nf
    rw [hCsq, hC3, hC4]
    ring_nf
  have hPfactor :
      modifiedNarayanaPolynomial 5 =
        (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) + t) * X + C (1 : ℝ)) *
          (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) - t) * X + C (1 : ℝ)) *
            (X - C c) := by
    rw [modifiedNarayanaPolynomial_five]
    dsimp [t, c]
    have ht_sq' : Real.sqrt (15 : ℝ) ^ 2 = (15 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hCsq : (C (Real.sqrt (15 : ℝ)) : ℝ[X]) ^ 2 = C (15 : ℝ) := by
      rw [← map_pow, ht_sq']
    have hC1 : (C (1 : ℝ) : ℝ[X]) = 1 := by simp
    have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
    have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 :=
      Polynomial.C_eq_natCast (R := ℝ) 15
    have hC50 : (C (50 : ℝ) : ℝ[X]) = 50 :=
      Polynomial.C_eq_natCast (R := ℝ) 50
    have hCneg1 : (C (-(1 : ℝ)) : ℝ[X]) = -1 := by simp
    rw [hC1, hC50, hCneg1]
    norm_num
    ring_nf
    rw [hCsq, hC7, hC15]
    ring_nf
  have hGdeg : (FiniteSkewBoard.auxiliaryG 5).natDegree = 4 := by
    rw [FiniteSkewBoard.auxiliaryG_five]
    compute_degree!
  have hG_ne : FiniteSkewBoard.auxiliaryG 5 ≠ 0 := by
    intro hzero
    rw [hzero] at hGdeg
    norm_num at hGdeg
  have hquadGA_deg :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) + s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadGA_ne :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) + s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadGA_deg
    norm_num at hquadGA_deg
  have hquadGB_deg :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) - s) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadGB_ne :
      (C (1 : ℝ) * X ^ 2 + C ((4 : ℝ) - s) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadGB_deg
    norm_num at hquadGB_deg
  have hquadPA_deg :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) + t) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadPA_ne :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) + t) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadPA_deg
    norm_num at hquadPA_deg
  have hquadPB_deg :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) - t) * X + C (1 : ℝ)).natDegree = 2 := by
    compute_degree!
  have hquadPB_ne :
      (C (1 : ℝ) * X ^ 2 + C ((7 : ℝ) - t) * X + C (1 : ℝ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hquadPB_deg
    norm_num at hquadPB_deg
  have hXc_ne : X - C c ≠ 0 := X_sub_C_ne_zero c
  have hs_sq : s ^ 2 = (3 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have ht_sq : t ^ 2 = (15 : ℝ) := by
    dsimp [t]
    exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.sqrt_nonneg _
  have hs_ge6div5 : (6 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_ge8div5 : (8 / 5 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_ge69div40 : (69 / 40 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs_le7div4 : s ≤ (7 / 4 : ℝ) := by
    dsimp [s]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs_le2 : s ≤ (2 : ℝ) := by linarith
  have ht_ge1 : (1 : ℝ) ≤ t := by
    dsimp [t]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have ht_ge15div4 : (15 / 4 : ℝ) ≤ t := by
    dsimp [t]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have ht_ge77div20 : (77 / 20 : ℝ) ≤ t := by
    dsimp [t]
    apply Real.le_sqrt_of_sq_le
    norm_num
  have ht_le31div8 : t ≤ (31 / 8 : ℝ) := by
    dsimp [t]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have ht_le4 : t ≤ (4 : ℝ) := by linarith
  have h15_sub_8s_nonneg : 0 ≤ (15 : ℝ) - 8 * s := by
    nlinarith only [hs_le7div4]
  have h60_sub_14t_nonneg : 0 ≤ (60 : ℝ) - 14 * t := by
    nlinarith only [ht_le4]
  have hα_sq : α ^ 2 = (15 : ℝ) + 8 * s := by
    dsimp [α]
    exact Real.sq_sqrt (by positivity)
  have hβ_sq : β ^ 2 = (15 : ℝ) - 8 * s := by
    dsimp [β]
    exact Real.sq_sqrt h15_sub_8s_nonneg
  have hγ_sq : γ ^ 2 = (60 : ℝ) + 14 * t := by
    dsimp [γ]
    exact Real.sq_sqrt (by positivity)
  have hδ_sq : δ ^ 2 = (60 : ℝ) - 14 * t := by
    dsimp [δ]
    exact Real.sq_sqrt h60_sub_14t_nonneg
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact Real.sqrt_nonneg _
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact Real.sqrt_nonneg _
  have hγ_nonneg : 0 ≤ γ := by
    dsimp [γ]
    exact Real.sqrt_nonneg _
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    exact Real.sqrt_nonneg _
  have hα_ge5 : (5 : ℝ) ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hs_ge8div5]
  have hα_ge21div4 : (21 / 4 : ℝ) ≤ α := by
    dsimp [α]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hs_ge8div5]
  have hα_le6 : α ≤ (6 : ℝ) := by
    dsimp [α]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_le7div4]
  have hα_le27div5 : α ≤ (27 / 5 : ℝ) := by
    dsimp [α]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_le7div4]
  have hβ_le3div2 : β ≤ (3 / 2 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_ge8div5]
  have hβ_le11div10 : β ≤ (11 / 10 : ℝ) := by
    dsimp [β]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hs_ge69div40]
  have hβ_ge1 : (1 : ℝ) ≤ β := by
    dsimp [β]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hs_le7div4]
  have hγ_ge3 : (3 : ℝ) ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_nonneg]
  have hγ_ge6 : (6 : ℝ) ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_nonneg]
  have hγ_ge533div50 : (533 / 50 : ℝ) ≤ γ := by
    dsimp [γ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_ge77div20]
  have hδ_ge2 : (2 : ℝ) ≤ δ := by
    dsimp [δ]
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ht_le4]
  have hδ_le5div2 : δ ≤ (5 / 2 : ℝ) := by
    dsimp [δ]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [ht_ge77div20]
  have hδ_le3 : δ ≤ (3 : ℝ) := by
    dsimp [δ]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [ht_ge15div4]
  have h2sβ_leα : 2 * s + β ≤ α := by
    linarith
  have h2tδ_leγ : 2 * t + δ ≤ γ := by
    linarith
  have htwo_sub_s_leβ : 2 - s ≤ β := by
    linarith only [hs_ge6div5, hβ_ge1]
  have hG_splits : (FiniteSkewBoard.auxiliaryG 5).Splits := by
    rw [hGfactor]
    refine (Polynomial.Splits.C (5 : ℝ)).mul ?_
    refine
      (quadraticPoly_splits_of_discrim_nonneg (by norm_num) ?_).mul
        (quadraticPoly_splits_of_discrim_nonneg (by norm_num) ?_)
    · norm_num [discrim]
      nlinarith only [hs_sq, hs_nonneg]
    · norm_num [discrim]
      nlinarith only [hs_sq, h15_sub_8s_nonneg]
  have hG_roots :
      (FiniteSkewBoard.auxiliaryG 5).roots = (↑[u, v, w, z] : Multiset ℝ) := by
    rw [hGfactor]
    rw [roots_mul
      (mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
        (mul_ne_zero hquadGA_ne hquadGB_ne))]
    rw [roots_C, roots_mul (mul_ne_zero hquadGA_ne hquadGB_ne)]
    have hdiscA : ((4 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (15 : ℝ) + 8 * s := by
      nlinarith only [hs_sq]
    have hdiscA_nonneg :
        0 ≤ ((4 : ℝ) + s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscA]
      positivity
    have hdiscB : ((4 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (15 : ℝ) - 8 * s := by
      nlinarith only [hs_sq]
    have hdiscB_nonneg :
        0 ≤ ((4 : ℝ) - s) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscB]
      exact h15_sub_8s_nonneg
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((4 : ℝ) + s))
      (c := (1 : ℝ)) (by norm_num) hdiscA_nonneg]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((4 : ℝ) - s))
      (c := (1 : ℝ)) (by norm_num) hdiscB_nonneg]
    rw [hdiscA, hdiscB]
    dsimp [u, v, w, z, α, β]
    norm_num
    change
      (↑[(s - 4 - Real.sqrt (15 - 8 * s)) / 2,
          (-s + -4 - Real.sqrt (15 + 8 * s)) / 2,
          (-s + -4 + Real.sqrt (15 + 8 * s)) / 2,
          (s - 4 + Real.sqrt (15 - 8 * s)) / 2] : Multiset ℝ) =
        ↑[(-4 - s - Real.sqrt (15 + 8 * s)) / 2,
          (-4 + s - Real.sqrt (15 - 8 * s)) / 2,
          (-4 + s + Real.sqrt (15 - 8 * s)) / 2,
          (-4 - s + Real.sqrt (15 + 8 * s)) / 2]
    rw [Multiset.coe_eq_coe]
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
      (List.Perm.trans (List.Perm.swap _ _ _)
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))))
  have hP_roots :
      (modifiedNarayanaPolynomial 5).roots = (↑[a, b, c, d, e] : Multiset ℝ) := by
    rw [hPfactor]
    rw [roots_mul (mul_ne_zero (mul_ne_zero hquadPA_ne hquadPB_ne) hXc_ne)]
    rw [roots_mul (mul_ne_zero hquadPA_ne hquadPB_ne)]
    have hdiscA : ((7 : ℝ) + t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (60 : ℝ) + 14 * t := by
      nlinarith only [ht_sq]
    have hdiscA_nonneg :
        0 ≤ ((7 : ℝ) + t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscA]
      positivity
    have hdiscB : ((7 : ℝ) - t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) =
        (60 : ℝ) - 14 * t := by
      nlinarith only [ht_sq]
    have hdiscB_nonneg :
        0 ≤ ((7 : ℝ) - t) ^ 2 - 4 * (1 : ℝ) * (1 : ℝ) := by
      rw [hdiscB]
      exact h60_sub_14t_nonneg
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((7 : ℝ) + t))
      (c := (1 : ℝ)) (by norm_num) hdiscA_nonneg]
    rw [roots_quadratic_posLead (a := (1 : ℝ)) (b := ((7 : ℝ) - t))
      (c := (1 : ℝ)) (by norm_num) hdiscB_nonneg]
    rw [roots_X_sub_C]
    rw [hdiscA, hdiscB]
    dsimp [a, b, c, d, e, γ, δ]
    norm_num
    change
      (↑[(t - 7 - Real.sqrt (60 - 14 * t)) / 2,
          (-t + -7 - Real.sqrt (60 + 14 * t)) / 2,
          (-t + -7 + Real.sqrt (60 + 14 * t)) / 2,
          (t - 7 + Real.sqrt (60 - 14 * t)) / 2,
          -1] : Multiset ℝ) =
        ↑[(-7 - t - Real.sqrt (60 + 14 * t)) / 2,
          (-7 + t - Real.sqrt (60 - 14 * t)) / 2,
          -1,
          (-7 + t + Real.sqrt (60 - 14 * t)) / 2,
          (-7 - t + Real.sqrt (60 + 14 * t)) / 2]
    rw [Multiset.coe_eq_coe]
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
      (List.Perm.trans (List.Perm.swap _ _ _)
        (List.Perm.cons _ (List.Perm.cons _ <|
          List.Perm.trans (List.Perm.swap _ _ _)
            (List.Perm.trans (List.Perm.cons _ (List.Perm.swap _ _ _))
              (List.Perm.swap _ _ _)))))
  have hP_ne : modifiedNarayanaPolynomial 5 ≠ 0 := modifiedNarayanaPolynomial_ne_zero 5
  have hP_splits : (modifiedNarayanaPolynomial 5).Splits :=
    modifiedNarayanaPolynomial_splits 5
  have hPdeg : (modifiedNarayanaPolynomial 5).natDegree = 5 := by
    rw [modifiedNarayanaPolynomial_natDegree]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hbc : b ≤ c := by
    dsimp [b, c]
    linarith
  have hcd : c ≤ d := by
    dsimp [c, d]
    linarith
  have hde : d ≤ e := by
    dsimp [d, e]
    linarith
  have huv : u ≤ v := by
    dsimp [u, v]
    linarith
  have hvw : v ≤ w := by
    dsimp [v, w]
    linarith
  have hwz : w ≤ z := by
    dsimp [w, z]
    linarith
  have hau : a ≤ u := by
    dsimp [a, u]
    linarith
  have hub : u ≤ b := by
    dsimp [u, b]
    linarith
  have hbv : b ≤ v := by
    dsimp [b, v]
    linarith
  have hvc : v ≤ c := by
    dsimp [v, c]
    linarith
  have hcw : c ≤ w := by
    dsimp [c, w]
    linarith
  have hwd : w ≤ d := by
    dsimp [w, d]
    linarith
  have hdz : d ≤ z := by
    dsimp [d, z]
    linarith
  have hze : z ≤ e := by
    dsimp [z, e]
    linarith
  exact interlaces_of_quartic_quintic_root_lists hP_ne hP_splits hG_ne hG_splits
    hPdeg hGdeg hP_roots hG_roots hab hbc hcd hde huv hvw hwz hau hub hbv hvc
    hcw hwd hdz hze

/-- The `n = 5` case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_five :
    Prec (FiniteSkewBoard.auxiliaryG 5) (modifiedNarayanaPolynomial 5) := by
  exact lemma33AuxiliaryGInterlaces_modified_five_interlaces.toPrec

/-- The checked initial cases `n = 1, 2, 3, 4, 5` of Braun--Jal Lemma 3.3, for
the concrete modified Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_five
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₅ : n ≤ 5) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three
  · exact lemma33AuxiliaryGInterlaces_modified_four
  · exact lemma33AuxiliaryGInterlaces_modified_five

/-- Conditional checked initial cases `n = 1, 2, 3, 4, 5, 6` of Braun--Jal
Lemma 3.3.  The only remaining input is the `P_6`/`G_6` cross-root
inequality package. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_six_of_crosses
    (hcross :
      ∀ {a b c d e r : ℝ},
        (modifiedNarayanaPolynomial 6).roots =
          (↑[a, b, c, d, e, r] : Multiset ℝ) →
        a ≤ b → b ≤ c → c ≤ d → d ≤ e → e ≤ r →
        ModifiedNarayanaSixAuxiliaryGCrossInequalities a b c d e r)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  interval_cases n
  · exact lemma33AuxiliaryGInterlaces_modified_base
  · exact lemma33AuxiliaryGInterlaces_modified_two
  · exact lemma33AuxiliaryGInterlaces_modified_three
  · exact lemma33AuxiliaryGInterlaces_modified_four
  · exact lemma33AuxiliaryGInterlaces_modified_five
  · exact lemma33AuxiliaryGInterlaces_modified_six_of_crosses hcross

/-- Conditional checked initial cases `n = 1, 2, 3, 4, 5, 6` of Braun--Jal
Lemma 3.3 from the single `P_6`/`G_6` sign certificate. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_six_of_eval_signs
    (hsign : ModifiedNarayanaSixAuxiliaryGSignCertificate)
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) :=
  lemma33AuxiliaryGInterlaces_modified_of_le_six_of_crosses
    (fun {a b c d e r} hP_roots hab hbc hcd hde her =>
      ModifiedNarayanaSixAuxiliaryGCrossInequalities.of_eval_signs
        (by simpa [modifiedNarayanaPolynomialSix] using hP_roots)
        hab hbc hcd hde her hsign)
    hn₁ hn₆

/-- The checked initial cases `n = 1, 2, 3, 4, 5, 6` of Braun--Jal
Lemma 3.3, for the concrete modified Narayana family and the finite-board
auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_of_le_six
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    Prec (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) :=
  lemma33AuxiliaryGInterlaces_modified_of_le_six_of_eval_signs
    modifiedNarayanaPolynomial_six_auxiliaryG_signCertificate hn₁ hn₆

/-- The checked initial cases `n = 1, ..., 6` of Braun--Jal Lemma 3.3,
packaged in the generic bounded interlacing interface. -/
theorem lemma33AuxiliaryGInterlaces_modified_upTo_six :
    Lemma33AuxiliaryGInterlacesUpToStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG 6 := by
  intro n hn₁ hn₆
  exact lemma33AuxiliaryGInterlaces_modified_of_le_six hn₁ hn₆

end GeneralizedSnakePosets
end RealRooted
