import RealRooted.CombinatorialExamples.Narayana
import RealRooted.GeneralizedSnakePosets.Statements
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Auxiliary
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

/-- Conditional consecutive interlacing for the concrete modified Narayana
family, inherited from the existing Narayana formalization. -/
theorem modifiedNarayanaPolynomial_strictInterl_succ_of_nonnegCoeffs
    (n : ℕ) (hnonneg : ∀ m : ℕ, HasNonnegCoeffs (narayanaQuot m)) :
    StrictInterl (modifiedNarayanaPolynomial n) (modifiedNarayanaPolynomial (n + 1)) := by
  simpa [modifiedNarayanaPolynomial] using
    (strictInterl_narayanaQuot_succ_of_nonnegCoeffs (n + 1) (by lia) hnonneg)

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

/-- Base interlacing relation between the first two modified Narayana
polynomials. -/
theorem modifiedNarayanaPolynomial_zero_strictInterl_one :
    StrictInterl (modifiedNarayanaPolynomial 0) (modifiedNarayanaPolynomial 1) :=
  modifiedNarayanaPolynomial_zero_interlaces_one.toStrictInterl

/-- The `n = 1` base case of Braun--Jal Lemma 3.3, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem lemma33AuxiliaryGInterlaces_modified_base :
    StrictInterl (FiniteSkewBoard.auxiliaryG 1) (modifiedNarayanaPolynomial 1) := by
  simpa [FiniteSkewBoard.auxiliaryG_one] using
    modifiedNarayanaPolynomial_zero_strictInterl_one

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

/-- The `m = 1` generalized Narayana polynomials satisfy the same normalized
recurrence as the quotient-style modified Narayana sequence. -/
theorem narayanaPolynomial_one_succ_succ (n : ℕ) :
    narayanaPolynomial 1 (n + 2) =
      narayanaCoeffA (n + 1) * narayanaPolynomial 1 (n + 1) +
        narayanaCoeffB (n + 1) * narayanaPolynomial 1 n := by
  have hrec := narayanaPolynomial_pure_rec 1 n
  have hden : (C ((n : ℝ) + 4) : ℝ[X]) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (by positivity)
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
