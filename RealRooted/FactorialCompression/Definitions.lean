import RealRooted.Basic.Coefficients
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Factorial-compression definitions

The finite coefficient compression, its adjacent differential step, and the
degree-changing kernel used by the main theorem.
-/

open Polynomial
open scoped BigOperators

noncomputable section
namespace RealRooted.FactorialCompression

def h (r : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (r / 2 + 1),
    C ((Nat.factorial r : ℝ) /
      ((Nat.factorial j : ℝ) * (Nat.factorial (r - 2 * j) : ℝ))) * X ^ j

def mu (N ell k : ℕ) : ℝ :=
  if 2 * k ≤ N + ell then
    (Nat.factorial (N - k) : ℝ) / (Nat.factorial (N + ell - 2 * k) : ℝ)
  else 0

def compression (N ell : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), C (mu N ell k * p.coeff k) * X ^ k

def nextPolynomial (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (X + C a) * p + X * p.derivative

def alpha (N ell : ℕ) (a : ℝ) : ℝ :=
  1 / 4 + a * ((N : ℝ) + 1) /
    (((N + ell : ℕ) : ℝ) * (((N + ell : ℕ) : ℝ) + 1))

def beta (N ell : ℕ) (a : ℝ) : ℝ :=
  ((N : ℝ) - (ell : ℝ) + 1) *
    (1 / 2 + a / (((N + ell : ℕ) : ℝ) + 1))

def kernel (N ell : ℕ) (a : ℝ) : ℝ[X] :=
  C (alpha N ell a) * h (N + ell) +
    (C (beta N ell a) * X - C (1 / 4 : ℝ)) *
      h (N + ell - 1)

end RealRooted.FactorialCompression
