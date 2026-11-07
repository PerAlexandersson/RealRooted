module

public import RealRooted.PFPolynomial
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Charpoly
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.DeterminantPencil

/-! # Pólya-frequency determinant pencils -/

public section

open Polynomial

namespace Matrix

/-- A totally nonnegative matrix gives a polynomial with nonnegative
coefficients by taking the determinant of `I + X A`. -/
theorem IsTotallyNonneg.hasNonnegCoeffs_det_one_add_X_smul
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg) :
    RealRooted.HasNonnegCoeffs (det (1 + (X : ℝ[X]) • A.map C)) := by
  intro k
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  exact Finset.sum_nonneg fun s _ => hA.principalMinor_nonneg s

/-- The normalized affine determinant of a totally nonnegative matrix is a
Pólya-frequency polynomial, including when the matrix is singular. -/
theorem IsTotallyNonneg.isPFPolynomial_det_one_add_X_smul
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg) :
    RealRooted.IsPFPolynomial (det (1 + (X : ℝ[X]) • A.map C)) := by
  apply RealRooted.IsPFPolynomial.of_realRooted_nonneg
    hA.hasNonnegCoeffs_det_one_add_X_smul
  rw [Matrix.det_one_add_X_smul_eq_reverse_charpoly_comp_neg_X]
  apply (Polynomial.Splits.reverse ?_).comp_of_natDegree_le_one
  · simp
  · exact hA.charpoly_splits

end Matrix
