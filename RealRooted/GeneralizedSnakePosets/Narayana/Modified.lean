import RealRooted.CombinatorialExamples.Narayana
import RealRooted.GeneralizedSnakePosets
import RealRooted.NarayanaTransformation

/-!
# Modified Narayana inputs for generalized snake posets

This module contains the concrete modified Narayana family used in the
Braun--Jal Section 3 interfaces and the coefficient-side model used to transport
between the quotient-style Narayana formalization and explicit coefficients.
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

/-- The quotient Narayana recurrence in the modified Narayana indexing. -/
theorem modifiedNarayanaPolynomial_succ_succ (n : ℕ) :
    modifiedNarayanaPolynomial (n + 2) =
      narayanaCoeffA (n + 1) * modifiedNarayanaPolynomial (n + 1) +
        narayanaCoeffB (n + 1) * modifiedNarayanaPolynomial n := by
  simp [modifiedNarayanaPolynomial, narayanaQuot_succ_succ]

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

@[simp] theorem modifiedNarayanaCoeffPolynomial_nine :
    modifiedNarayanaCoeffPolynomial 9 =
      1 + C (45 : ℝ) * X + C (540 : ℝ) * X ^ 2 +
        C (2520 : ℝ) * X ^ 3 + C (5292 : ℝ) * X ^ 4 +
          C (5292 : ℝ) * X ^ 5 + C (2520 : ℝ) * X ^ 6 +
            C (540 : ℝ) * X ^ 7 + C (45 : ℝ) * X ^ 8 + X ^ 9 := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 9 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia, show k ≠ 5 by lia,
      show k ≠ 6 by lia, show k ≠ 7 by lia, show k ≠ 8 by lia,
      show k ≠ 9 by lia]

@[simp] theorem modifiedNarayanaCoeffPolynomial_ten :
    modifiedNarayanaCoeffPolynomial 10 =
      1 + C (55 : ℝ) * X + C (825 : ℝ) * X ^ 2 +
        C (4950 : ℝ) * X ^ 3 + C (13860 : ℝ) * X ^ 4 +
          C (19404 : ℝ) * X ^ 5 + C (13860 : ℝ) * X ^ 6 +
            C (4950 : ℝ) * X ^ 7 + C (825 : ℝ) * X ^ 8 +
              C (55 : ℝ) * X ^ 9 + X ^ 10 := by
  ext k
  by_cases hk : k ≤ 10
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 10 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia, show k ≠ 5 by lia,
      show k ≠ 6 by lia, show k ≠ 7 by lia, show k ≠ 8 by lia,
      show k ≠ 9 by lia, show k ≠ 10 by lia]

@[simp] theorem modifiedNarayanaCoeffPolynomial_eleven :
    modifiedNarayanaCoeffPolynomial 11 =
      1 + C (66 : ℝ) * X + C (1210 : ℝ) * X ^ 2 +
        C (9075 : ℝ) * X ^ 3 + C (32670 : ℝ) * X ^ 4 +
          C (60984 : ℝ) * X ^ 5 + C (60984 : ℝ) * X ^ 6 +
            C (32670 : ℝ) * X ^ 7 + C (9075 : ℝ) * X ^ 8 +
              C (1210 : ℝ) * X ^ 9 + C (66 : ℝ) * X ^ 10 + X ^ 11 := by
  ext k
  by_cases hk : k ≤ 11
  · interval_cases k <;>
      norm_num [modifiedNarayanaCoeffPolynomial, narayanaTransformCoeff, Nat.choose,
        coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
  · have hklt : 11 < k := Nat.lt_of_not_ge hk
    simp [modifiedNarayanaCoeffPolynomial, coeff_narayanaPolynomial_of_lt hklt,
      coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
      show k ≠ 0 by lia, show (1 : ℕ) ≠ k by lia, show k ≠ 2 by lia,
      show k ≠ 3 by lia, show k ≠ 4 by lia, show k ≠ 5 by lia,
      show k ≠ 6 by lia, show k ≠ 7 by lia, show k ≠ 8 by lia,
      show k ≠ 9 by lia, show k ≠ 10 by lia, show k ≠ 11 by lia]

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

/-- Reversed-index coefficient formula for the quotient-style modified
Narayana polynomial. -/
theorem modifiedNarayanaPolynomial_coeff_sub (n i : ℕ) (hi : i ≤ n) :
    (modifiedNarayanaPolynomial n).coeff (n - i) =
      narayanaTransformCoeff 1 n i := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial]
  exact coeff_narayanaPolynomial_sub 1 n i hi

/-- The coefficient immediately below the leading coefficient of `P_n`. -/
theorem modifiedNarayanaPolynomial_coeff_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (modifiedNarayanaPolynomial n).coeff (n - 1) =
      (n : ℝ) * (n + 1) / 2 := by
  rw [modifiedNarayanaPolynomial_coeff_sub n 1 hn]
  simp [narayanaTransformCoeff, Nat.choose_one_right, Nat.cast_add]

/-- The coefficient two places below the leading coefficient of `P_n`. -/
theorem modifiedNarayanaPolynomial_coeff_sub_two (n : ℕ) (hn : 2 ≤ n) :
    (modifiedNarayanaPolynomial n).coeff (n - 2) =
      (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 - 1) / 12 := by
  rw [modifiedNarayanaPolynomial_coeff_sub n 2 hn]
  simp only [narayanaTransformCoeff, Nat.cast_choose_two]
  push_cast
  ring

/-- The next coefficient of the positive-degree modified Narayana polynomial. -/
theorem modifiedNarayanaPolynomial_nextCoeff (n : ℕ) (hn : 1 ≤ n) :
    (modifiedNarayanaPolynomial n).nextCoeff =
      (n : ℝ) * (n + 1) / 2 := by
  rw [nextCoeff_of_natDegree_pos]
  · rw [modifiedNarayanaPolynomial_natDegree,
      modifiedNarayanaPolynomial_coeff_sub_one n hn]
  · rw [modifiedNarayanaPolynomial_natDegree]
    lia

/-- Consecutive modified Narayana polynomials have no common real root. -/
theorem modifiedNarayanaPolynomial_no_common_root (n : ℕ) :
    ∀ r : ℝ, (modifiedNarayanaPolynomial (n + 1)).IsRoot r →
      ¬ (modifiedNarayanaPolynomial n).IsRoot r := by
  intro r hr hprev
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial] at hr
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial] at hprev
  exact narayanaPolynomial_no_common_root 1 n r hr hprev

/-! ## Explicit low-degree normal forms -/

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
    (modifiedNarayanaPolynomial 6).natDegree = 6 :=
  modifiedNarayanaPolynomial_natDegree 6

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

@[simp] theorem modifiedNarayanaPolynomial_nine :
    modifiedNarayanaPolynomial 9 =
      1 + C (45 : ℝ) * X + C (540 : ℝ) * X ^ 2 +
        C (2520 : ℝ) * X ^ 3 + C (5292 : ℝ) * X ^ 4 +
          C (5292 : ℝ) * X ^ 5 + C (2520 : ℝ) * X ^ 6 +
            C (540 : ℝ) * X ^ 7 + C (45 : ℝ) * X ^ 8 + X ^ 9 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_nine]

@[simp] theorem modifiedNarayanaPolynomial_ten :
    modifiedNarayanaPolynomial 10 =
      1 + C (55 : ℝ) * X + C (825 : ℝ) * X ^ 2 +
        C (4950 : ℝ) * X ^ 3 + C (13860 : ℝ) * X ^ 4 +
          C (19404 : ℝ) * X ^ 5 + C (13860 : ℝ) * X ^ 6 +
            C (4950 : ℝ) * X ^ 7 + C (825 : ℝ) * X ^ 8 +
              C (55 : ℝ) * X ^ 9 + X ^ 10 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_ten]

@[simp] theorem modifiedNarayanaPolynomial_eleven :
    modifiedNarayanaPolynomial 11 =
      1 + C (66 : ℝ) * X + C (1210 : ℝ) * X ^ 2 +
        C (9075 : ℝ) * X ^ 3 + C (32670 : ℝ) * X ^ 4 +
          C (60984 : ℝ) * X ^ 5 + C (60984 : ℝ) * X ^ 6 +
            C (32670 : ℝ) * X ^ 7 + C (9075 : ℝ) * X ^ 8 +
              C (1210 : ℝ) * X ^ 9 + C (66 : ℝ) * X ^ 10 + X ^ 11 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial,
    modifiedNarayanaCoeffPolynomial_eleven]

end GeneralizedSnakePosets
end RealRooted
