module

public import RealRooted.MultiplierSequence
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import RealRooted.Laguerre.NegativeParameters
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.Ring

/-!
# Jensen polynomials of the regularized Bessel coefficients

The reciprocal-Gamma identity remains valid at every parameter, including
Gamma poles. The Laguerre normalization is the one in O'Sullivan, Section 3.3,
with `generalizedLaguerre d alpha = d! L_d^alpha(-X)`.
-/

public section

open Polynomial

namespace RealRooted

/-- The Jensen polynomial of the regularized Bessel coefficients is a scalar
multiple of the classical-sign Laguerre polynomial. No Gamma factor is cancelled. -/
theorem jensenPolynomial_inv_gamma_eq (d : ℕ) (alpha : ℝ) :
    jensenPolynomial d (fun k ↦ (-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹) =
      C ((Real.Gamma (alpha + d + 1))⁻¹) *
        (generalizedLaguerre d alpha).comp (-X) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_C_mul, coeff_comp_neg_X, coeff_generalizedLaguerre]
  by_cases hk : k ≤ d
  · simp only [ite_eq_left hk]
    have hgamma := Real.inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add
      (alpha + k + 1) (d - k)
    have harg : alpha + (k : ℝ) + 1 + ((d - k : ℕ) : ℝ) = alpha + d + 1 := by
      rw [Nat.cast_sub hk]
      ring
    rw [harg] at hgamma
    rw [hgamma]
    ring
  · simp only [ite_eq_right hk, mul_zero, zero_mul]

/-- Every Jensen polynomial of the regularized Bessel coefficients splits
for parameters at least `-2`, including both Gamma-pole endpoints. -/
theorem jensenPolynomial_inv_gamma_splits (d : ℕ) {alpha : ℝ}
    (halpha : -2 ≤ alpha) :
    (jensenPolynomial d
      (fun k ↦ (-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹)).Splits := by
  rw [jensenPolynomial_inv_gamma_eq]
  exact (Splits.C _).mul (generalizedLaguerre_splits_of_neg_two_le d halpha).comp_neg_X

end RealRooted
