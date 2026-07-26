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

/-- The `n = 2` case of Braun--Jal equation (2), for the quotient-style
modified Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_two :
    X * FiniteSkewBoard.auxiliaryG 1 =
      modifiedNarayanaPolynomial 2 -
        (1 + X) * modifiedNarayanaPolynomial 1 := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial 1,
    modifiedNarayanaPolynomial_eq_coeffPolynomial 2]
  exact narayanaCoeffAuxiliaryGRecurrence_modified_two

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

end GeneralizedSnakePosets
end RealRooted
