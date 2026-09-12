import RealRooted.GarloffWagner.Theorem12
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Factorial coefficient sequences

This file connects finite Pólya-frequency polynomials to multiplier
sequences.  The Jensen polynomial of the factorial-weighted coefficient
sequence is a Garloff--Wagner Schur product with `(X + 1) ^ n`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The Jensen polynomial of the factorial-weighted coefficients is a
Garloff--Wagner Schur product with a binomial polynomial. -/
theorem jensenPolynomial_factorial_mul_coeff_eq_gwSchurProduct
    (p : ℝ[X]) (n : ℕ) :
    jensenPolynomial n (fun k => (k.factorial : ℝ) * p.coeff k) =
      gwSchurProduct p ((X + 1 : ℝ[X]) ^ n) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_gwSchurProduct,
    Polynomial.coeff_X_add_one_pow]
  split_ifs with hk
  · ring
  · rw [Nat.choose_eq_zero_of_lt (not_le.mp hk)]
    simp

/-- Every Jensen polynomial of the factorial-weighted coefficients of a PF
polynomial is again PF. -/
theorem IsPFPolynomial.isPF_jensenPolynomial_factorial_mul_coeff
    {p : ℝ[X]} (hp : IsPFPolynomial p) (n : ℕ) :
    IsPFPolynomial
      (jensenPolynomial n (fun k => (k.factorial : ℝ) * p.coeff k)) := by
  rw [jensenPolynomial_factorial_mul_coeff_eq_gwSchurProduct]
  exact gwSchurProductPF hp (isPFPolynomial_X_add_one.pow n)

/-- The factorial-weighted coefficient sequence of a PF polynomial is a PF
multiplier sequence. -/
theorem IsPFPolynomial.isPFMultiplierSequence_factorial_mul_coeff
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFMultiplierSequence (fun k => (k.factorial : ℝ) * p.coeff k) := by
  rw [isPFMultiplierSequence_iff_jensenPolynomial_isPF]
  exact hp.isPF_jensenPolynomial_factorial_mul_coeff

end RealRooted
