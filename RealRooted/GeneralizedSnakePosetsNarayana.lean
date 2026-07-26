import RealRooted.CombinatorialExamples.Narayana
import RealRooted.GeneralizedSnakePosets

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

/-- Base case `n = 1` of Braun--Jal equation (2), for the concrete modified
Narayana family and the finite-board auxiliary `G`. -/
theorem narayanaAuxiliaryGRecurrence_modified_base :
    X * FiniteSkewBoard.auxiliaryG 0 =
      modifiedNarayanaPolynomial 1 - (1 + X) * modifiedNarayanaPolynomial 0 := by
  rw [FiniteSkewBoard.auxiliaryG_zero]
  simp

end GeneralizedSnakePosets
end RealRooted
