import RealRooted.JacobiDeformation.AppellJacobiOperator

/-!
# Concrete Jacobi transport of the finite Appell kernel

This module uses ordinary univariate polynomial differentiation.  The library
Jacobi operator is the negative of the positive operator in the proof note.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The Bernstein monomial used in the concrete Jacobi transport. -/
def jacobiBernstein (i j : ℕ) : ℝ[X] := X ^ i * (1 - X) ^ j

/-- The library Jacobi operator on a Bernstein monomial.  It is the negative
of the positive `D` in the proof note, hence the three signs are reversed. -/
theorem jacobiDifferentialOperator_jacobiBernstein (c d : ℝ) (i j : ℕ) :
    jacobiDifferentialOperator c (c + d) (jacobiBernstein i j) =
      C ((i : ℝ) * ((i : ℝ) + c - 1)) * jacobiBernstein (i - 1) j +
        C ((j : ℝ) * ((j : ℝ) + d - 1)) * jacobiBernstein i (j - 1) -
          C (((i + j : ℕ) : ℝ) * ((i + j : ℕ) + c + d - 1)) *
            jacobiBernstein i j := by
  cases i with
  | zero =>
      cases j with
      | zero =>
          simp [jacobiBernstein, jacobiDifferentialOperator]
      | succ j =>
          simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
            derivative_X_pow_succ, derivative_pow, pow_succ]
          ring
  | succ i =>
      cases j with
      | zero =>
          simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
            derivative_X_pow_succ, derivative_pow, pow_succ]
          ring
      | succ j =>
          simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
            derivative_X_pow_succ, derivative_pow, pow_succ]
          ring

end RealRooted.JacobiDeformation
