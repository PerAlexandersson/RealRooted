module

public import RealRooted.CombinatorialExamples.Narayana
public import RealRooted.GeneralizedSnakePosets.Statements
public import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Auxiliary
public import RealRooted.NarayanaTransformation
import RealRooted.NarayanaTransformation.Recurrences.Interlacing
import RealRooted.NarayanaTransformation.Recurrences.Identities
import RealRooted.NarayanaTransformation.Rectangular.Preservation
import RealRooted.NarayanaTransformation.Rectangular.Narayana
import RealRooted.Linear

/-!
# Modified Narayana inputs for generalized snake posets

This module contains the concrete modified Narayana family used in the
combinatorial interfaces and the coefficient-side model used to transport
between the quotient-style Narayana formalization and explicit coefficients.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Concrete modified Narayana family -/

/-- The modified Narayana polynomial `P_n = t^{-1} N_{n+1}` of Braun--Jal,
where `N_{n+1}` is the Narayana polynomial.  It is defined as the Narayana
quotient `narayanaQuot (n + 1)`, so `P_0 = 1` and `P_1 = 1 + X`. -/
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

/-- `modifiedNarayanaPolynomial` is the Braun--Jal modified Narayana family:
`P_0 = 1` and `N_{n+1} = X * P_n`, i.e. `P_n(t) = t^{-1} N_{n+1}(t)`. -/
theorem modifiedNarayanaFamily_narayana :
    modifiedNarayanaPolynomial 0 = 1 ∧
      ∀ n : ℕ, narayana (n + 1) = X * modifiedNarayanaPolynomial n := by
  constructor
  · simp [modifiedNarayanaPolynomial]
  · intro n
    simp [modifiedNarayanaPolynomial, narayana]

/-- Consecutive modified Narayana polynomials strictly interlace. -/
theorem modifiedNarayanaPolynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (modifiedNarayanaPolynomial n) (modifiedNarayanaPolynomial (n + 1)) :=
  strictInterl_narayanaQuot_succ (n + 1) (by lia)

/-- Consecutive modified Narayana polynomials interlace. -/
theorem modifiedNarayanaPolynomial_interlaces_succ (n : ℕ) :
    Interlaces (modifiedNarayanaPolynomial n) (modifiedNarayanaPolynomial (n + 1)) :=
  interlaces_narayanaQuot_succ (n + 1) (by lia)

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

/-- The `n = 1` base case of the auxiliary interlacing lemma, for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem auxiliaryGInterlaces_modified_base :
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

/-- The first nontrivial interlacing check for the coefficient-side
modified Narayana family. -/
theorem modifiedNarayanaCoeffPolynomial_one_strictInterl_two :
    StrictInterl (modifiedNarayanaCoeffPolynomial 1)
      (modifiedNarayanaCoeffPolynomial 2) := by
  simpa [modifiedNarayanaCoeffPolynomial] using
    (strictInterl_narayanaPolynomial_one_two 1)

/-- The first nontrivial interlacing check for the coefficient-side modified
Narayana family. -/
theorem modifiedNarayanaCoeffPolynomial_one_interlaces_two :
    Interlaces (modifiedNarayanaCoeffPolynomial 1)
      (modifiedNarayanaCoeffPolynomial 2) :=
  modifiedNarayanaCoeffPolynomial_one_strictInterl_two.toInterlaces (by
    rw [modifiedNarayanaCoeffPolynomial_natDegree,
      modifiedNarayanaCoeffPolynomial_natDegree])

/-- The quotient-style and coefficient-side modified Narayana models agree. -/
theorem modifiedNarayanaPolynomial_eq_coeffPolynomial (n : ℕ) :
    modifiedNarayanaPolynomial n = modifiedNarayanaCoeffPolynomial n :=
  narayanaQuot_succ_eq_narayanaPolynomial_one n

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

end GeneralizedSnakePosets
end RealRooted
