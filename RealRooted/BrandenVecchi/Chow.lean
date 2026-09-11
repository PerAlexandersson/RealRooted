import RealRooted.LowerTriangularMatrix
import RealRooted.Mathlib.Algebra.Polynomial.Chow

/-!
# Chow polynomials of lower-triangular matrices

This module gives the literal recursive matrix construction in Corollary 3.1
of Brändén--Vecchi, *Chow polynomials of totally nonnegative matrices and
posets* (2025).  The characterization by reflection, and its total-nonnegative
real-rootedness consequences, are intentionally separate later layers.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The Chow-derangement polynomial sequence associated to a real
lower-triangular matrix.

The successor clause is the paper's recursion
`dₙ = X * Sₙ₋₁ (∑ k < n, rₙₖ dₖ)`. -/
def chowDerangement (R : LowerTriangularMatrix ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      X * Polynomial.chowS n (∑ k : Fin (n + 1),
        C (R (n + 1) k) * chowDerangement R k)
  termination_by n => n
  decreasing_by exact k.isLt

/-- The Chow polynomial in row `n`, formed from the Chow-derangement sequence. -/
def chowPolynomial (R : LowerTriangularMatrix ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (R n k) * chowDerangement R k

@[simp]
theorem chowDerangement_zero (R : LowerTriangularMatrix ℝ) : chowDerangement R 0 = 1 := by
  simp [chowDerangement]

/-- The defining successor recursion for the Chow-derangement sequence. -/
theorem chowDerangement_succ (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    chowDerangement R (n + 1) =
      X * Polynomial.chowS n (∑ k : Fin (n + 1),
        C (R (n + 1) k) * chowDerangement R k) := by
  simp [chowDerangement]

/-- The defining row expansion for the Chow polynomial. -/
theorem chowPolynomial_eq (R : LowerTriangularMatrix ℝ) (n : ℕ) :
    chowPolynomial R n = ∑ k ∈ Finset.range (n + 1), C (R n k) * chowDerangement R k :=
  rfl

/-- A unit entry at the initial diagonal position gives the expected initial
Chow polynomial. -/
theorem chowPolynomial_zero (R : LowerTriangularMatrix ℝ) (hdiag : R 0 0 = 1) :
    chowPolynomial R 0 = 1 := by
  rw [chowPolynomial_eq]
  simp [hdiag]

end

end RealRooted.BrandenVecchi
