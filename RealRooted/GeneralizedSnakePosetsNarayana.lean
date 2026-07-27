import RealRooted.CombinatorialExamples.Narayana
import RealRooted.GeneralizedSnakePosets
import RealRooted.NarayanaTransformation

/-!
# Narayana inputs for generalized snake posets

This module connects the Braun--Jal generalized-snake-poset statement
interfaces to the existing Narayana polynomial formalization.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Concrete modified Narayana family -/

/-- The modified Narayana family `P_n = t^{-1} N_{n+1}` from Braun--Jal
Section 3, reusing the existing Narayana quotient sequence. -/
def modifiedNarayanaPolynomial (n : ℕ) : ℝ[X] :=
  narayanaQuot (n + 1)

@[simp] theorem modifiedNarayanaPolynomial_zero :
    modifiedNarayanaPolynomial 0 = 1 := by
  simp [modifiedNarayanaPolynomial]

@[simp] theorem modifiedNarayanaPolynomial_one :
    modifiedNarayanaPolynomial 1 = 1 + X := by
  norm_num [modifiedNarayanaPolynomial, narayanaQuot_two, narayanaCoeffA,
    narayanaCoeffB]

/-- The modified Narayana polynomial `P_n` has degree `n`. -/
theorem modifiedNarayanaPolynomial_natDegree (n : ℕ) :
    (modifiedNarayanaPolynomial n).natDegree = n := by
  simpa [modifiedNarayanaPolynomial] using
    (natDegree_narayanaQuot (n + 1) (by lia))

/-- The modified Narayana polynomial `P_n` is monic. -/
theorem modifiedNarayanaPolynomial_leadingCoeff (n : ℕ) :
    (modifiedNarayanaPolynomial n).leadingCoeff = 1 := by
  simpa [modifiedNarayanaPolynomial] using
    (leadingCoeff_narayanaQuot (n + 1) (by lia))

/-- Modified Narayana polynomials are nonzero. -/
theorem modifiedNarayanaPolynomial_ne_zero (n : ℕ) :
    modifiedNarayanaPolynomial n ≠ 0 := by
  simpa [modifiedNarayanaPolynomial] using
    (narayanaQuot_ne_zero (n + 1) (by lia))

/-- Modified Narayana polynomials have positive leading coefficient. -/
theorem modifiedNarayanaPolynomial_posLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (modifiedNarayanaPolynomial n) := by
  simpa [modifiedNarayanaPolynomial] using
    (narayanaQuot_posLeadingCoeff (n + 1) (by lia))

/-- The existing Narayana sequence and `modifiedNarayanaPolynomial` satisfy the
Braun--Jal modified-family interface. -/
theorem modifiedNarayanaFamily_narayana :
    ModifiedNarayanaFamilyStatement narayana modifiedNarayanaPolynomial := by
  constructor
  · simp [modifiedNarayanaPolynomial]
  · intro n
    simp [modifiedNarayanaPolynomial, narayana]

/-- Conditional consecutive proper position for the concrete modified Narayana
family, inherited from the existing Narayana formalization. -/
theorem modifiedNarayanaPolynomial_prec_succ_of_nonnegCoeffs
    (n : ℕ) (hnonneg : ∀ m : ℕ, HasNonnegCoeffs (narayanaQuot m)) :
    Prec (modifiedNarayanaPolynomial n) (modifiedNarayanaPolynomial (n + 1)) := by
  simpa [modifiedNarayanaPolynomial] using
    (prec_narayanaQuot_succ_of_nonnegCoeffs (n + 1) (by lia) hnonneg)

/-- Conditional consecutive interlacing for the concrete modified Narayana
family, inherited from the existing Narayana formalization. -/
theorem modifiedNarayanaPolynomial_interlaces_succ_of_nonnegCoeffs
    (n : ℕ) (hnonneg : ∀ m : ℕ, HasNonnegCoeffs (narayanaQuot m)) :
    Interlaces (modifiedNarayanaPolynomial n)
      (modifiedNarayanaPolynomial (n + 1)) := by
  simpa [modifiedNarayanaPolynomial] using
    (interlaces_narayanaQuot_succ_of_nonnegCoeffs (n + 1) (by lia) hnonneg)

/-- Base interlacing between the first two modified Narayana polynomials. -/
theorem modifiedNarayanaPolynomial_zero_interlaces_one :
    Interlaces (modifiedNarayanaPolynomial 0) (modifiedNarayanaPolynomial 1) := by
  rw [modifiedNarayanaPolynomial_zero, modifiedNarayanaPolynomial_one]
  simpa [add_comm] using
    interlaces_one_linear (p := X + C (1 : ℝ))
      (Polynomial.natDegree_X_add_C (x := (1 : ℝ)))

/-- Base proper-position relation between the first two modified Narayana
polynomials. -/
theorem modifiedNarayanaPolynomial_zero_prec_one :
    Prec (modifiedNarayanaPolynomial 0) (modifiedNarayanaPolynomial 1) :=
  modifiedNarayanaPolynomial_zero_interlaces_one.toPrec

/-- The `n = 1` base case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_base :
    Prec (FiniteSkewBoard.auxiliaryG 1) (modifiedNarayanaPolynomial 1) := by
  simpa [FiniteSkewBoard.auxiliaryG_one] using
    modifiedNarayanaPolynomial_zero_prec_one

/-- Base case `n = 1` of Braun--Jal equation (2), for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_base :
    X * FiniteSkewBoard.auxiliaryG 0 =
      modifiedNarayanaPolynomial 1 - (1 + X) * modifiedNarayanaPolynomial 0 := by
  rw [FiniteSkewBoard.auxiliaryG_zero]
  simp

/-! ## Coefficient-side modified Narayana family -/

/-- Coefficient-side model of the modified Narayana family, using the already
formalized generalized Narayana polynomial with `m = 1`. -/
def modifiedNarayanaCoeffPolynomial (n : ℕ) : ℝ[X] :=
  narayanaPolynomial 1 n

/-- The coefficient-side modified Narayana polynomial has nonnegative
coefficients. -/
theorem modifiedNarayanaCoeffPolynomial_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (modifiedNarayanaCoeffPolynomial n) :=
  hasNonnegCoeffs_narayanaPolynomial 1 n

/-- The coefficient-side modified Narayana polynomial has degree `n`. -/
theorem modifiedNarayanaCoeffPolynomial_natDegree (n : ℕ) :
    (modifiedNarayanaCoeffPolynomial n).natDegree = n :=
  natDegree_narayanaPolynomial 1 n

/-- The coefficient-side modified Narayana polynomial is monic. -/
theorem modifiedNarayanaCoeffPolynomial_leadingCoeff (n : ℕ) :
    (modifiedNarayanaCoeffPolynomial n).leadingCoeff = 1 :=
  leadingCoeff_narayanaPolynomial 1 n

/-- Coefficient-side modified Narayana polynomials are nonzero. -/
theorem modifiedNarayanaCoeffPolynomial_ne_zero (n : ℕ) :
    modifiedNarayanaCoeffPolynomial n ≠ 0 :=
  narayanaPolynomial_ne_zero 1 n

/-- Coefficient-side modified Narayana polynomials have positive leading
coefficient. -/
theorem modifiedNarayanaCoeffPolynomial_posLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (modifiedNarayanaCoeffPolynomial n) :=
  hasPosLeadingCoeff_narayanaPolynomial 1 n

@[simp] theorem modifiedNarayanaCoeffPolynomial_zero :
    modifiedNarayanaCoeffPolynomial 0 = 1 := by
  simp [modifiedNarayanaCoeffPolynomial]

@[simp] theorem modifiedNarayanaCoeffPolynomial_one :
    modifiedNarayanaCoeffPolynomial 1 = 1 + X := by
  rw [modifiedNarayanaCoeffPolynomial, narayanaPolynomial_one]
  simp [add_comm]

@[simp] theorem modifiedNarayanaCoeffPolynomial_two :
    modifiedNarayanaCoeffPolynomial 2 = 1 + C (3 : ℝ) * X + X ^ 2 := by
  rw [modifiedNarayanaCoeffPolynomial, narayanaPolynomial_two]
  norm_num
  ring_nf

@[simp] theorem modifiedNarayanaCoeffPolynomial_three :
    modifiedNarayanaCoeffPolynomial 3 =
      1 + C (6 : ℝ) * X + C (6 : ℝ) * X ^ 2 + X ^ 3 := by
  ext k
  by_cases hk : k ≤ 3
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 3 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia]

@[simp] theorem modifiedNarayanaCoeffPolynomial_four :
    modifiedNarayanaCoeffPolynomial 4 =
      1 + C (10 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
        C (10 : ℝ) * X ^ 3 + X ^ 4 := by
  ext k
  by_cases hk : k ≤ 4
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 4 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia]

@[simp] theorem modifiedNarayanaCoeffPolynomial_five :
    modifiedNarayanaCoeffPolynomial 5 =
      1 + C (15 : ℝ) * X + C (50 : ℝ) * X ^ 2 +
        C (50 : ℝ) * X ^ 3 + C (15 : ℝ) * X ^ 4 + X ^ 5 := by
  ext k
  by_cases hk : k ≤ 5
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 5 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia, show k ≠ 5 by lia]

@[simp] theorem modifiedNarayanaCoeffPolynomial_six :
    modifiedNarayanaCoeffPolynomial 6 =
      1 + C (21 : ℝ) * X + C (105 : ℝ) * X ^ 2 +
        C (175 : ℝ) * X ^ 3 + C (105 : ℝ) * X ^ 4 +
          C (21 : ℝ) * X ^ 5 + X ^ 6 := by
  ext k
  by_cases hk : k ≤ 6
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 6 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia, show k ≠ 5 by lia,
      show k ≠ 6 by lia]

/-- The first nontrivial proper-position check for the coefficient-side
modified Narayana family. -/
theorem modifiedNarayanaCoeffPolynomial_one_prec_two :
    Prec (modifiedNarayanaCoeffPolynomial 1)
      (modifiedNarayanaCoeffPolynomial 2) := by
  simpa [modifiedNarayanaCoeffPolynomial] using
    (prec_narayanaPolynomial_one_two 1)

/-- The first nontrivial interlacing check for the coefficient-side modified
Narayana family. -/
theorem modifiedNarayanaCoeffPolynomial_one_interlaces_two :
    Interlaces (modifiedNarayanaCoeffPolynomial 1)
      (modifiedNarayanaCoeffPolynomial 2) :=
  modifiedNarayanaCoeffPolynomial_one_prec_two.toInterlaces (by
    rw [modifiedNarayanaCoeffPolynomial_natDegree,
      modifiedNarayanaCoeffPolynomial_natDegree])

/-- Base case `n = 1` of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_base :
    X * FiniteSkewBoard.auxiliaryG 0 =
      modifiedNarayanaCoeffPolynomial 1 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 0 := by
  rw [FiniteSkewBoard.auxiliaryG_zero]
  simp

/-- The `n = 2` case of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_two :
    X * FiniteSkewBoard.auxiliaryG 1 =
      modifiedNarayanaCoeffPolynomial 2 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 1 := by
  rw [FiniteSkewBoard.auxiliaryG_one, modifiedNarayanaCoeffPolynomial_one,
    modifiedNarayanaCoeffPolynomial_two]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 :=
    Polynomial.C_eq_natCast (R := ℝ) 3
  rw [hC3]
  ring_nf

/-- The `n = 3` case of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_three :
    X * FiniteSkewBoard.auxiliaryG 2 =
      modifiedNarayanaCoeffPolynomial 3 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 2 := by
  rw [FiniteSkewBoard.auxiliaryG_two, modifiedNarayanaCoeffPolynomial_two,
    modifiedNarayanaCoeffPolynomial_three]
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_eq_natCast (R := ℝ) 2
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  rw [hC2, hC3, hC6]
  ring_nf

/-- The `n = 4` Braun--Jal equation (2) reduces to the concrete `G_3`
finite-board computation. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_four_of_auxiliaryG_three
    (hG3 : FiniteSkewBoard.auxiliaryG 3 =
      3 + C (8 : ℝ) * X + C (3 : ℝ) * X ^ 2) :
    X * FiniteSkewBoard.auxiliaryG 3 =
      modifiedNarayanaCoeffPolynomial 4 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 3 := by
  rw [hG3, modifiedNarayanaCoeffPolynomial_three,
    modifiedNarayanaCoeffPolynomial_four]
  have hC3 : (C (3 : ℝ) : ℝ[X]) = 3 := Polynomial.C_eq_natCast (R := ℝ) 3
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC8 : (C (8 : ℝ) : ℝ[X]) = 8 := Polynomial.C_eq_natCast (R := ℝ) 8
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 := Polynomial.C_eq_natCast (R := ℝ) 10
  have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 := Polynomial.C_eq_natCast (R := ℝ) 20
  rw [hC3, hC6, hC8, hC10, hC20]
  ring_nf

/-- The `n = 4` case of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_four :
    X * FiniteSkewBoard.auxiliaryG 3 =
      modifiedNarayanaCoeffPolynomial 4 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 3 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_four_of_auxiliaryG_three
    FiniteSkewBoard.auxiliaryG_three

/-- The `n = 5` Braun--Jal equation (2) reduces to the concrete `G_4`
finite-board computation. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_five_of_auxiliaryG_four
    (hG4 : FiniteSkewBoard.auxiliaryG 4 =
      4 + C (20 : ℝ) * X + C (20 : ℝ) * X ^ 2 + C (4 : ℝ) * X ^ 3) :
    X * FiniteSkewBoard.auxiliaryG 4 =
      modifiedNarayanaCoeffPolynomial 5 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 4 := by
  rw [hG4, modifiedNarayanaCoeffPolynomial_four,
    modifiedNarayanaCoeffPolynomial_five]
  have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := Polynomial.C_eq_natCast (R := ℝ) 4
  have hC10 : (C (10 : ℝ) : ℝ[X]) = 10 := Polynomial.C_eq_natCast (R := ℝ) 10
  have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 := Polynomial.C_eq_natCast (R := ℝ) 15
  have hC20 : (C (20 : ℝ) : ℝ[X]) = 20 := Polynomial.C_eq_natCast (R := ℝ) 20
  have hC50 : (C (50 : ℝ) : ℝ[X]) = 50 := Polynomial.C_eq_natCast (R := ℝ) 50
  rw [hC4, hC10, hC15, hC20, hC50]
  ring_nf

/-- The `n = 5` case of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_five :
    X * FiniteSkewBoard.auxiliaryG 4 =
      modifiedNarayanaCoeffPolynomial 5 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 4 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_five_of_auxiliaryG_four
    FiniteSkewBoard.auxiliaryG_four

/-- The `n = 6` Braun--Jal equation (2) reduces to the concrete `G_5`
finite-board computation. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (hG5 : FiniteSkewBoard.auxiliaryG 5 =
      5 + C (40 : ℝ) * X + C (75 : ℝ) * X ^ 2 +
        C (40 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4) :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaCoeffPolynomial 6 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 5 := by
  rw [hG5, modifiedNarayanaCoeffPolynomial_five,
    modifiedNarayanaCoeffPolynomial_six]
  have hC5 : (C (5 : ℝ) : ℝ[X]) = 5 := Polynomial.C_eq_natCast (R := ℝ) 5
  have hC15 : (C (15 : ℝ) : ℝ[X]) = 15 :=
    Polynomial.C_eq_natCast (R := ℝ) 15
  have hC21 : (C (21 : ℝ) : ℝ[X]) = 21 :=
    Polynomial.C_eq_natCast (R := ℝ) 21
  have hC40 : (C (40 : ℝ) : ℝ[X]) = 40 :=
    Polynomial.C_eq_natCast (R := ℝ) 40
  have hC50 : (C (50 : ℝ) : ℝ[X]) = 50 :=
    Polynomial.C_eq_natCast (R := ℝ) 50
  have hC75 : (C (75 : ℝ) : ℝ[X]) = 75 :=
    Polynomial.C_eq_natCast (R := ℝ) 75
  have hC105 : (C (105 : ℝ) : ℝ[X]) = 105 :=
    Polynomial.C_eq_natCast (R := ℝ) 105
  have hC175 : (C (175 : ℝ) : ℝ[X]) = 175 :=
    Polynomial.C_eq_natCast (R := ℝ) 175
  rw [hC5, hC15, hC21, hC40, hC50, hC75, hC105, hC175]
  ring_nf

/-- The `n = 6` Braun--Jal equation (2) reduces to the remaining three-row
and four-row truncated-staircase rook-polynomial computations. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_six_of_staircase_five_tail
    (h53 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 3 =
      1 + C (12 : ℝ) * X + C (25 : ℝ) * X ^ 2 + C (10 : ℝ) * X ^ 3)
    (h54 : FiniteSkewBoard.truncatedStaircaseRookPolynomial 5 4 =
      1 + C (14 : ℝ) * X + C (40 : ℝ) * X ^ 2 +
        C (30 : ℝ) * X ^ 3 + C (5 : ℝ) * X ^ 4) :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaCoeffPolynomial 6 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 5 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_truncatedStaircaseRookPolynomial_five_three_four
      h53 h54)

/-- The `n = 6` Braun--Jal equation (2) reduces to the bottom-row expansions
for the two remaining `n = 5` truncated-staircase rook-polynomial rows. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_six_of_bottom_row_expansions
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
      modifiedNarayanaCoeffPolynomial 6 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 5 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_bottom_row_expansions
      hbottom53 hbottom54)

/-- The `n = 6` Braun--Jal equation (2) reduces to the named bottom-row
expansion predicate for the two remaining `n = 5` truncated-staircase rows. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_six_of_bottom_row_expansion_statements
    (hbottom53 : FiniteSkewBoard.truncatedStaircaseBottomRowExpansion 5 2)
    (hbottom54 : FiniteSkewBoard.truncatedStaircaseBottomRowExpansion 5 3) :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaCoeffPolynomial 6 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 5 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    (FiniteSkewBoard.auxiliaryG_five_of_bottom_row_expansion_statements
      hbottom53 hbottom54)

/-- The `m = 1` generalized Narayana polynomials satisfy the same normalized
recurrence as the quotient-style modified Narayana sequence. -/
theorem narayanaPolynomial_one_succ_succ (n : ℕ) :
    narayanaPolynomial 1 (n + 2) =
      narayanaCoeffA (n + 1) * narayanaPolynomial 1 (n + 1) +
        narayanaCoeffB (n + 1) * narayanaPolynomial 1 n := by
  have hrec := narayanaPolynomial_pure_rec 1 n
  have hden : (C ((n : ℝ) + 4) : ℝ[X]) ≠ 0 := by
    exact Polynomial.C_ne_zero.mpr (by positivity)
  have hA : C ((n : ℝ) + 4) * narayanaCoeffA (n + 1) =
      C ((2 * n : ℝ) + 5) * (1 + X) := by
    unfold narayanaCoeffA
    have hden_cast : (((n + 1 : ℕ) : ℝ) + 3) = (n : ℝ) + 4 := by
      push_cast
      ring
    have hscalar : ((n : ℝ) + 4) *
        ((2 * ((n + 1 : ℕ) : ℝ) + 3) /
          (((n + 1 : ℕ) : ℝ) + 3)) = (2 * n : ℝ) + 5 := by
      rw [hden_cast]
      field_simp [show ((n : ℝ) + 4) ≠ 0 by positivity]
      push_cast
      ring
    rw [← mul_assoc, ← map_mul, hscalar]
  have hB : C ((n : ℝ) + 4) * narayanaCoeffB (n + 1) =
      -C ((n : ℝ) + 1) * (1 - X) ^ 2 := by
    unfold narayanaCoeffB
    have hden_cast : (((n + 1 : ℕ) : ℝ) + 3) = (n : ℝ) + 4 := by
      push_cast
      ring
    have hscalar : ((n : ℝ) + 4) *
        (-((n + 1 : ℕ) : ℝ) /
          (((n + 1 : ℕ) : ℝ) + 3)) = -((n : ℝ) + 1) := by
      rw [hden_cast]
      field_simp [show ((n : ℝ) + 4) ≠ 0 by positivity]
      push_cast
      ring
    rw [← mul_assoc, ← map_mul, hscalar, map_neg]
  apply mul_left_cancel₀ hden
  rw [mul_add]
  rw [← mul_assoc, hA, ← mul_assoc, hB]
  convert hrec using 1 <;> ring_nf

/-- The quotient-style and coefficient-side modified Narayana models agree. -/
theorem modifiedNarayanaPolynomial_eq_coeffPolynomial (n : ℕ) :
    modifiedNarayanaPolynomial n = modifiedNarayanaCoeffPolynomial n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih_succ =>
      change narayanaQuot (n + 3) = narayanaPolynomial 1 (n + 2)
      have ih' : narayanaQuot (n + 1) = narayanaPolynomial 1 n := by
        simpa [modifiedNarayanaPolynomial, modifiedNarayanaCoeffPolynomial] using ih
      have ih_succ' :
          narayanaQuot (n + 2) = narayanaPolynomial 1 (n + 1) := by
        simpa [modifiedNarayanaPolynomial, modifiedNarayanaCoeffPolynomial,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih_succ
      rw [narayanaQuot_succ_succ (n + 1), narayanaPolynomial_one_succ_succ n,
        ih', ih_succ']

/-- The quotient Narayana sequence has nonnegative coefficients, via the
coefficient-side model. -/
theorem narayanaQuot_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (narayanaQuot n) := by
  cases n with
  | zero => simp [HasNonnegCoeffs]
  | succ n =>
      have heq : narayanaQuot (n + 1) = narayanaPolynomial 1 n := by
        simpa [modifiedNarayanaPolynomial, modifiedNarayanaCoeffPolynomial]
          using modifiedNarayanaPolynomial_eq_coeffPolynomial n
      rw [heq]
      exact hasNonnegCoeffs_narayanaPolynomial 1 n

/-- Modified Narayana polynomials have nonnegative coefficients. -/
theorem modifiedNarayanaPolynomial_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (modifiedNarayanaPolynomial n) := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial n]
  exact modifiedNarayanaCoeffPolynomial_hasNonnegCoeffs n

@[simp] theorem modifiedNarayanaPolynomial_two :
    modifiedNarayanaPolynomial 2 = 1 + C (3 : ℝ) * X + X ^ 2 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_two]

@[simp] theorem modifiedNarayanaPolynomial_three :
    modifiedNarayanaPolynomial 3 =
      1 + C (6 : ℝ) * X + C (6 : ℝ) * X ^ 2 + X ^ 3 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_three]

@[simp] theorem modifiedNarayanaPolynomial_four :
    modifiedNarayanaPolynomial 4 =
      1 + C (10 : ℝ) * X + C (20 : ℝ) * X ^ 2 +
        C (10 : ℝ) * X ^ 3 + X ^ 4 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_four]

@[simp] theorem modifiedNarayanaPolynomial_five :
    modifiedNarayanaPolynomial 5 =
      1 + C (15 : ℝ) * X + C (50 : ℝ) * X ^ 2 +
        C (50 : ℝ) * X ^ 3 + C (15 : ℝ) * X ^ 4 + X ^ 5 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_five]

@[simp] theorem modifiedNarayanaPolynomial_six :
    modifiedNarayanaPolynomial 6 =
      1 + C (21 : ℝ) * X + C (105 : ℝ) * X ^ 2 +
        C (175 : ℝ) * X ^ 3 + C (105 : ℝ) * X ^ 4 +
          C (21 : ℝ) * X ^ 5 + X ^ 6 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_six]

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

end GeneralizedSnakePosets
end RealRooted
