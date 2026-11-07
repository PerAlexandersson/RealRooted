module

public import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.ElementaryPositivity
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import RealRooted.Basic.Coefficients

/-! # Negative real zeros of parity-compatible skew Schur specializations -/

public section

open Polynomial Matrix

namespace RealRooted.Schur

/-- The constant value of an elementary-coordinate specialization is the unmodified
skew Jacobi–Trudi determinant. -/
@[simp] theorem elementarySubstitution_eval_zero {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (h k : Fin n → ℕ) (r : ℤ) :
    (elementarySubstitution s a h k r).eval 0 = (elementaryMatrix s a h k).det := by
  simp [elementarySubstitution, eval_det]

variable {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → ℝ)
  (ha : ∀ i ∈ s, 0 ≤ a i) {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k)
  (hkh : ∀ i, k i ≤ h i)
  (hsize : ∀ i, h i ≤ k i + (s.filter fun j => 0 < a j).card)
  (r : ℤ)
  (hpar : ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r → Even (i.val + j.val))

include ha hh hk hkh hsize hpar

/-- The alphabet-size and parity hypotheses suffice for the PF conclusion;
no determinant-positivity hypothesis is left to the caller. -/
theorem elementarySubstitution_isPFPolynomial_of_nonneg :
    IsPFPolynomial (elementarySubstitution s a h k r) :=
  elementarySubstitution_isPFPolynomial s a ha hh hk r
    (det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize) hpar

/-- Parity-compatible skew elementary-coordinate specializations are nonzero and split
completely over the reals, including the constant and empty-shape cases. -/
theorem elementarySubstitution_isRealRooted :
    elementarySubstitution s a h k r ≠ 0 ∧ (elementarySubstitution s a h k r).Splits := by
  have hp := elementarySubstitution_isPFPolynomial_of_nonneg s a ha hh hk hkh hsize r hpar
  apply hp.ne_zero_and_splits
  intro hz
  have he := congrArg (fun p : ℝ[X] => p.eval 0) hz
  simp only [elementarySubstitution_eval_zero, eval_zero] at he
  exact (det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize).ne' he

/-- Every root of the parity-compatible skew Schur specialization is strictly negative. -/
theorem roots_elementarySubstitution_neg :
    ∀ x ∈ (elementarySubstitution s a h k r).roots, x < 0 := by
  apply roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (elementarySubstitution_isPFPolynomial_of_nonneg s a ha hh hk hkh hsize r hpar).hasNonnegCoeffs
  rw [coeff_zero_eq_eval_zero, elementarySubstitution_eval_zero]
  exact (det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize).ne'

end RealRooted.Schur
