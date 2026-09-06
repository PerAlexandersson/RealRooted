import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The multivariate Euler operator

This file packages the sum in Euler's homogeneous identity as an operator.
-/

open scoped BigOperators

namespace MvPolynomial

/-- The multivariate Euler operator `∑ i, X i * ∂/∂X i`. -/
noncomputable def eulerOperator {σ R : Type*} [Fintype σ] [CommSemiring R]
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i : σ, X i * pderiv i P

/-- Euler's identity expressed using `eulerOperator`. -/
theorem IsHomogeneous.eulerOperator_eq {σ R : Type*}
    [Fintype σ] [CommSemiring R] {P : MvPolynomial σ R} {n : ℕ}
    (hP : P.IsHomogeneous n) :
    eulerOperator P = n • P := by
  exact hP.sum_X_mul_pderiv

/-- Euler's identity with the natural scalar written as a constant
polynomial. -/
theorem IsHomogeneous.eulerOperator_eq_C_mul {σ R : Type*}
    [Fintype σ] [CommSemiring R] {P : MvPolynomial σ R} {n : ℕ}
    (hP : P.IsHomogeneous n) :
    eulerOperator P = C (n : R) * P := by
  rw [hP.eulerOperator_eq]
  simp [nsmul_eq_mul]

end MvPolynomial
