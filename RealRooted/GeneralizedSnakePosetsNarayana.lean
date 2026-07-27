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

@[simp] theorem modifiedNarayanaCoeffPolynomial_seven :
    modifiedNarayanaCoeffPolynomial 7 =
      1 + C (28 : ℝ) * X + C (196 : ℝ) * X ^ 2 +
        C (490 : ℝ) * X ^ 3 + C (490 : ℝ) * X ^ 4 +
          C (196 : ℝ) * X ^ 5 + C (28 : ℝ) * X ^ 6 + X ^ 7 := by
  ext k
  by_cases hk : k ≤ 7
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 7 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia, show k ≠ 5 by lia,
      show k ≠ 6 by lia, show k ≠ 7 by lia]

@[simp] theorem modifiedNarayanaCoeffPolynomial_eight :
    modifiedNarayanaCoeffPolynomial 8 =
      1 + C (36 : ℝ) * X + C (336 : ℝ) * X ^ 2 +
        C (1176 : ℝ) * X ^ 3 + C (1764 : ℝ) * X ^ 4 +
          C (1176 : ℝ) * X ^ 5 + C (336 : ℝ) * X ^ 6 +
            C (36 : ℝ) * X ^ 7 + X ^ 8 := by
  ext k
  by_cases hk : k ≤ 8
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 8 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia, show k ≠ 5 by lia,
      show k ≠ 6 by lia, show k ≠ 7 by lia, show k ≠ 8 by lia]

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

/-- The `n = 6` case of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_six :
    X * FiniteSkewBoard.auxiliaryG 5 =
      modifiedNarayanaCoeffPolynomial 6 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 5 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_six_of_auxiliaryG_five
    FiniteSkewBoard.auxiliaryG_five

/-- The `n = 7` Braun--Jal equation (2) reduces to the concrete `G_6`
finite-board computation. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_seven_of_auxiliaryG_six
    (hG6 : FiniteSkewBoard.auxiliaryG 6 =
      6 + C (70 : ℝ) * X + C (210 : ℝ) * X ^ 2 +
        C (210 : ℝ) * X ^ 3 + C (70 : ℝ) * X ^ 4 +
          C (6 : ℝ) * X ^ 5) :
    X * FiniteSkewBoard.auxiliaryG 6 =
      modifiedNarayanaCoeffPolynomial 7 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 6 := by
  rw [hG6, modifiedNarayanaCoeffPolynomial_six,
    modifiedNarayanaCoeffPolynomial_seven]
  have hC6 : (C (6 : ℝ) : ℝ[X]) = 6 := Polynomial.C_eq_natCast (R := ℝ) 6
  have hC21 : (C (21 : ℝ) : ℝ[X]) = 21 :=
    Polynomial.C_eq_natCast (R := ℝ) 21
  have hC28 : (C (28 : ℝ) : ℝ[X]) = 28 :=
    Polynomial.C_eq_natCast (R := ℝ) 28
  have hC70 : (C (70 : ℝ) : ℝ[X]) = 70 :=
    Polynomial.C_eq_natCast (R := ℝ) 70
  have hC105 : (C (105 : ℝ) : ℝ[X]) = 105 :=
    Polynomial.C_eq_natCast (R := ℝ) 105
  have hC175 : (C (175 : ℝ) : ℝ[X]) = 175 :=
    Polynomial.C_eq_natCast (R := ℝ) 175
  have hC196 : (C (196 : ℝ) : ℝ[X]) = 196 :=
    Polynomial.C_eq_natCast (R := ℝ) 196
  have hC210 : (C (210 : ℝ) : ℝ[X]) = 210 :=
    Polynomial.C_eq_natCast (R := ℝ) 210
  have hC490 : (C (490 : ℝ) : ℝ[X]) = 490 :=
    Polynomial.C_eq_natCast (R := ℝ) 490
  rw [hC6, hC21, hC28, hC70, hC105, hC175, hC196, hC210, hC490]
  ring_nf

/-- The `n = 7` case of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_seven :
    X * FiniteSkewBoard.auxiliaryG 6 =
      modifiedNarayanaCoeffPolynomial 7 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 6 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_seven_of_auxiliaryG_six
    FiniteSkewBoard.auxiliaryG_six

/-- The `n = 8` Braun--Jal equation (2) reduces to the concrete `G_7`
finite-board computation. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_eight_of_auxiliaryG_seven
    (hG7 : FiniteSkewBoard.auxiliaryG 7 =
      7 + C (112 : ℝ) * X + C (490 : ℝ) * X ^ 2 +
        C (784 : ℝ) * X ^ 3 + C (490 : ℝ) * X ^ 4 +
          C (112 : ℝ) * X ^ 5 + C (7 : ℝ) * X ^ 6) :
    X * FiniteSkewBoard.auxiliaryG 7 =
      modifiedNarayanaCoeffPolynomial 8 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 7 := by
  rw [hG7, modifiedNarayanaCoeffPolynomial_seven,
    modifiedNarayanaCoeffPolynomial_eight]
  have hC7 : (C (7 : ℝ) : ℝ[X]) = 7 := Polynomial.C_eq_natCast (R := ℝ) 7
  have hC28 : (C (28 : ℝ) : ℝ[X]) = 28 :=
    Polynomial.C_eq_natCast (R := ℝ) 28
  have hC36 : (C (36 : ℝ) : ℝ[X]) = 36 :=
    Polynomial.C_eq_natCast (R := ℝ) 36
  have hC112 : (C (112 : ℝ) : ℝ[X]) = 112 :=
    Polynomial.C_eq_natCast (R := ℝ) 112
  have hC196 : (C (196 : ℝ) : ℝ[X]) = 196 :=
    Polynomial.C_eq_natCast (R := ℝ) 196
  have hC336 : (C (336 : ℝ) : ℝ[X]) = 336 :=
    Polynomial.C_eq_natCast (R := ℝ) 336
  have hC490 : (C (490 : ℝ) : ℝ[X]) = 490 :=
    Polynomial.C_eq_natCast (R := ℝ) 490
  have hC784 : (C (784 : ℝ) : ℝ[X]) = 784 :=
    Polynomial.C_eq_natCast (R := ℝ) 784
  have hC1176 : (C (1176 : ℝ) : ℝ[X]) = 1176 :=
    Polynomial.C_eq_natCast (R := ℝ) 1176
  have hC1764 : (C (1764 : ℝ) : ℝ[X]) = 1764 :=
    Polynomial.C_eq_natCast (R := ℝ) 1764
  rw [hC7, hC28, hC36, hC112, hC196, hC336, hC490, hC784, hC1176,
    hC1764]
  ring_nf

/-- The `n = 8` case of Braun--Jal equation (2), for the coefficient-side
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_eight :
    X * FiniteSkewBoard.auxiliaryG 7 =
      modifiedNarayanaCoeffPolynomial 8 -
        (1 + X) * modifiedNarayanaCoeffPolynomial 7 :=
  narayanaCoeffAuxiliaryGRecurrence_modified_eight_of_auxiliaryG_seven
    FiniteSkewBoard.auxiliaryG_seven

/-- The checked initial cases through `n = 6` of Braun--Jal equation (2), for
the coefficient-side modified Narayana family and finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_of_le_six
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₆ : n ≤ 6) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaCoeffPolynomial n -
        (1 + X) * modifiedNarayanaCoeffPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_base
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_two
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_three
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_four
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_five
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_six

/-- The checked initial cases through `n = 7` of Braun--Jal equation (2), for
the coefficient-side modified Narayana family and finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_of_le_seven
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₇ : n ≤ 7) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaCoeffPolynomial n -
        (1 + X) * modifiedNarayanaCoeffPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_base
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_two
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_three
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_four
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_five
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_six
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_seven

/-- The checked initial cases through `n = 8` of Braun--Jal equation (2), for
the coefficient-side modified Narayana family and finite-board auxiliary `G`. -/
theorem narayanaCoeffAuxiliaryGRecurrence_modified_of_le_eight
    {n : ℕ} (hn₁ : 1 ≤ n) (hn₈ : n ≤ 8) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaCoeffPolynomial n -
        (1 + X) * modifiedNarayanaCoeffPolynomial (n - 1) := by
  interval_cases n
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_base
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_two
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_three
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_four
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_five
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_six
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_seven
  · exact narayanaCoeffAuxiliaryGRecurrence_modified_eight

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

/-- Degree of the `P_6` modified Narayana polynomial. -/
theorem modifiedNarayanaPolynomial_six_natDegree :
    (modifiedNarayanaPolynomial 6).natDegree = 6 := by
  rw [modifiedNarayanaPolynomial_natDegree]

/-- The `P_6` modified Narayana polynomial is nonzero. -/
theorem modifiedNarayanaPolynomial_six_ne_zero : modifiedNarayanaPolynomial 6 ≠ 0 :=
  modifiedNarayanaPolynomial_ne_zero 6

@[simp] theorem modifiedNarayanaPolynomial_seven :
    modifiedNarayanaPolynomial 7 =
      1 + C (28 : ℝ) * X + C (196 : ℝ) * X ^ 2 +
        C (490 : ℝ) * X ^ 3 + C (490 : ℝ) * X ^ 4 +
          C (196 : ℝ) * X ^ 5 + C (28 : ℝ) * X ^ 6 + X ^ 7 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_seven]

@[simp] theorem modifiedNarayanaPolynomial_eight :
    modifiedNarayanaPolynomial 8 =
      1 + C (36 : ℝ) * X + C (336 : ℝ) * X ^ 2 +
        C (1176 : ℝ) * X ^ 3 + C (1764 : ℝ) * X ^ 4 +
          C (1176 : ℝ) * X ^ 5 + C (336 : ℝ) * X ^ 6 +
            C (36 : ℝ) * X ^ 7 + X ^ 8 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_eight]

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

/-- Cross-root inequalities between an ordered `P_6` root list and the named
`G_6` roots. -/
def ModifiedNarayanaSixAuxiliaryGCrossInequalities
    (a b c d e r : ℝ) : Prop :=
  a ≤ auxiliaryG_six_root0 ∧ auxiliaryG_six_root0 ≤ b ∧
    b ≤ auxiliaryG_six_root1 ∧ auxiliaryG_six_root1 ≤ c ∧
      c ≤ auxiliaryG_six_root2 ∧ auxiliaryG_six_root2 ≤ d ∧
        d ≤ auxiliaryG_six_root3 ∧ auxiliaryG_six_root3 ≤ e ∧
          e ≤ auxiliaryG_six_root4 ∧ auxiliaryG_six_root4 ≤ r

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

end GeneralizedSnakePosets
end RealRooted
