module

public import RealRooted.MultiplierSequence
import RealRooted.Basic
import Mathlib.Algebra.Polynomial.Derivative
import RealRooted.Derivative.Interlacing

/-!
# Derivatives of Jensen polynomials

Differentiation lowers the degree parameter and shifts the coefficient sequence.
-/

public section

open Polynomial

namespace RealRooted

/-- Differentiating a Jensen polynomial shifts its coefficient sequence by one. -/
theorem derivative_jensenPolynomial (d : ℕ) (gamma : ℕ → ℝ) :
    (jensenPolynomial (d + 1) gamma).derivative =
      C (d + 1 : ℝ) * jensenPolynomial d (fun k => gamma (k + 1)) := by
  ext k
  simp only [coeff_derivative, coeff_jensenPolynomial, coeff_C_mul]
  by_cases hk : k ≤ d
  · rw [ite_eq_left (by lia), ite_eq_left hk]
    have hc : ((d + 1).choose (k + 1) : ℝ) * (k + 1) =
        (d + 1) * (d.choose k : ℝ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq d k).symm
    linear_combination gamma (k + 1) * hc
  · rw [ite_eq_right (by lia), ite_eq_right hk]
    ring

/-- A nonzero final coefficient makes the degree parameter exact. -/
theorem natDegree_jensenPolynomial {d : ℕ} {gamma : ℕ → ℝ} (hd : gamma d ≠ 0) :
    (jensenPolynomial d gamma).natDegree = d :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_jensenPolynomial_le d gamma)
    (by simpa using hd)

/-- Consecutive degree and shift parameters weakly interlace whenever the larger
Jensen polynomial splits. The zero-aware relation covers vanishing coefficients. -/
theorem jensenPolynomial_shift_interl {d : ℕ} {gamma : ℕ → ℝ}
    (h : (jensenPolynomial (d + 1) gamma).Splits) :
    Interl (jensenPolynomial d (fun k => gamma (k + 1)))
      (jensenPolynomial (d + 1) gamma) := by
  have hi : Interl (jensenPolynomial (d + 1) gamma).derivative
      (jensenPolynomial (d + 1) gamma) := by
    by_cases hd : (jensenPolynomial (d + 1) gamma).natDegree = 0
    · rw [derivative_eq_zero.mpr hd]
      exact interl_zero_left _
    · exact (derivative_interlaces_of_natDegree_ne_zero h hd).toStrictInterl.toInterl
  have hscaled := hi.C_mul_left_of_nonneg (a := (d + 1 : ℝ)⁻¹) (by positivity)
  simpa only [derivative_jensenPolynomial, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (by positivity : (d + 1 : ℝ) ≠ 0), C_1, one_mul] using hscaled

end RealRooted
