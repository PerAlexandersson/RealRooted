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

theorem subdivisionRow_interlacing_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted
      (subdivisionRow (resolutionOfTotallyNonneg R hunit hR) n) :=
  subdivisionRow_interlacing (resolutionOfTotallyNonneg R hunit hR) n

theorem chainPolynomial_eq_zero_or_splits_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    chainPolynomial R n = 0 ∨ (chainPolynomial R n).Splits :=
  chainPolynomial_eq_zero_or_splits
    (resolutionOfTotallyNonneg R hunit hR) n

theorem chainPolynomial_hasNonnegCoeffs_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    HasNonnegCoeffs (chainPolynomial R n) :=
  chainPolynomial_hasNonnegCoeffs (resolutionOfTotallyNonneg R hunit hR) n

theorem roots_chainPolynomial_mem_Icc_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    ∀ x ∈ (chainPolynomial R n).roots, x ∈ Set.Icc (-1) 0 :=
  roots_chainPolynomial_mem_Icc (resolutionOfTotallyNonneg R hunit hR) n

/-- The zero-aware form is the unconditional interlacing conclusion: for the
identity matrix, some chain polynomials vanish. -/
theorem prec0_chainPolynomial_succ_of_isTotallyNonneg
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    Prec0 (chainPolynomial R n) (chainPolynomial R (n + 1)) :=
  prec0_chainPolynomial_succ (resolutionOfTotallyNonneg R hunit hR) n

theorem prec_chainPolynomial_succ_of_isTotallyNonneg_of_ne
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ)
    (hn : chainPolynomial R n ≠ 0)
    (hsucc : chainPolynomial R (n + 1) ≠ 0) :
    Prec (chainPolynomial R n) (chainPolynomial R (n + 1)) :=
  prec_chainPolynomial_succ_of_ne
    (resolutionOfTotallyNonneg R hunit hR) n hn hsucc

end RealRooted.BrandenLeite
