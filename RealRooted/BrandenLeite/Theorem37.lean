import RealRooted.BrandenLeite.ChainPolynomial
import RealRooted.BrandenLeite.WhitneyReduction

/-!
# Brändén--Saud Leite Theorem 3.7

This file discharges the total-nonnegativity hypothesis of the conditional
chain-polynomial theorem by constructing its canonical Whitney resolution.
-/

open Matrix Polynomial

noncomputable section

namespace RealRooted.BrandenLeite

variable {R : LowerTriangularMatrix ℝ}

/-- For a lower-unitriangular totally nonnegative matrix, every row of its
canonical Whitney resolution is sent by the subdivision operator to a weak
zero-aware interlacing sequence with nonnegative coefficients and real-rooted
nonzero members. -/
theorem subdivisionRow_interlacing_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (subdivisionRow (resolutionOfTotallyNonneg R hunit hR) n) :=
  subdivisionRow_interlacing (resolutionOfTotallyNonneg R hunit hR) n

/-- Brändén--Saud Leite Theorem 3.7: every chain polynomial of a
lower-unitriangular totally nonnegative matrix is zero or real-rooted. -/
theorem chainPolynomial_eq_zero_or_splits_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    chainPolynomial R n = 0 ∨ (chainPolynomial R n).Splits :=
  chainPolynomial_eq_zero_or_splits
    (resolutionOfTotallyNonneg R hunit hR) n

/-- Every chain polynomial of a lower-unitriangular totally nonnegative matrix
has nonnegative coefficients. -/
theorem chainPolynomial_hasNonnegCoeffs_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    HasNonnegCoeffs (chainPolynomial R n) :=
  chainPolynomial_hasNonnegCoeffs (resolutionOfTotallyNonneg R hunit hR) n

/-- Brändén--Saud Leite Theorem 3.7: every root of a chain polynomial of a
lower-unitriangular totally nonnegative matrix lies in `[-1, 0]`. -/
theorem roots_chainPolynomial_mem_Icc_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    ∀ x ∈ (chainPolynomial R n).roots, x ∈ Set.Icc (-1) 0 :=
  roots_chainPolynomial_mem_Icc (resolutionOfTotallyNonneg R hunit hR) n

/-- Brändén--Saud Leite Theorem 3.7: consecutive chain polynomials of a
lower-unitriangular totally nonnegative matrix interlace.  The conclusion uses
the zero-aware relation `Interl` because some chain polynomials can vanish, for
example those of the identity matrix. -/
theorem interl_chainPolynomial_succ_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    Interl (chainPolynomial R n) (chainPolynomial R (n + 1)) :=
  interl_chainPolynomial_succ (resolutionOfTotallyNonneg R hunit hR) n

/-- Consecutive chain polynomials of a lower-unitriangular totally
nonnegative matrix satisfy `StrictInterl` when both are nonzero. -/
theorem strictInterl_chainPolynomial_succ_of_isTotallyNonneg_of_ne
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ)
    (hn : chainPolynomial R n ≠ 0)
    (hsucc : chainPolynomial R (n + 1) ≠ 0) :
    StrictInterl (chainPolynomial R n) (chainPolynomial R (n + 1)) :=
  strictInterl_chainPolynomial_succ_of_ne
    (resolutionOfTotallyNonneg R hunit hR) n hn hsucc

end RealRooted.BrandenLeite
