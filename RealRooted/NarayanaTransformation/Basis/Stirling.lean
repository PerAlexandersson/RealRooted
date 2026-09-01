import RealRooted.NarayanaTransformation.Basis
import Mathlib.Combinatorics.Enumerative.Stirling

open Polynomial

noncomputable section

namespace RealRooted

/-- The coefficients of the unit-step rising factorial are the unsigned
Stirling numbers of the first kind. -/
theorem coeff_risingFactorialPolynomial_one : ∀ n k : ℕ,
    (risingFactorialPolynomial 1 n).coeff k = (Nat.stirlingFirst n k : ℝ)
  | 0, 0 => by simp [risingFactorialPolynomial]
  | 0, k + 1 => by
      rw [show risingFactorialPolynomial 1 0 = 1 by
        simp [risingFactorialPolynomial], coeff_one]
      simp
  | n + 1, 0 => by
      rw [risingFactorialPolynomial_succ_shift]
      simp [Nat.stirlingFirst_succ_zero]
  | n + 1, k + 1 => by
      rw [risingFactorialPolynomial_succ_mul, mul_add, coeff_add,
        coeff_mul_X, coeff_mul_C, coeff_risingFactorialPolynomial_one,
        coeff_risingFactorialPolynomial_one]
      exact_mod_cast (by
        simpa [add_comm, mul_comm] using (Nat.stirlingFirst_succ_succ n k).symm)

end RealRooted
