module

public import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.ElementaryPositivity
import RealRooted.TotallyNonnegPencil.CornerInterlacing
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-! # Negative real zeros of parity-compatible elementary determinant specializations -/

public section

open Polynomial Matrix

namespace RealRooted.Schur

/-- The constant value of an elementary-coordinate specialization is the unmodified
dual Jacobi–Trudi determinant. -/
@[simp] theorem elementarySubstitution_eval_zero {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (h k : Fin n → ℕ) (r : ℤ) :
    (elementarySubstitution s a h k r).eval 0 = (elementaryMatrix s a h k).det := by
  simp [elementarySubstitution, eval_det]

/-- The alphabet-size hypotheses make the constant term of the specialization nonzero. -/
theorem elementarySubstitution_eval_zero_ne_zero {ι : Type*} {n : ℕ} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) {h k : Fin n → ℕ} (hh : Antitone h)
    (hk : Antitone k) (hkh : ∀ i, k i ≤ h i)
    (hsize : ∀ i, h i ≤ k i + (s.filter fun j => 0 < a j).card) (r : ℤ) :
    (elementarySubstitution s a h k r).eval 0 ≠ 0 := by
  rw [elementarySubstitution_eval_zero]
  exact (det_elementaryMatrix_pos_of_nonneg s a ha hh hk hkh hsize).ne'

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

/-- Parity-compatible elementary-coordinate specializations are nonzero and split
completely over the reals, including the constant and empty-shape cases. -/
theorem elementarySubstitution_isRealRooted :
    elementarySubstitution s a h k r ≠ 0 ∧ (elementarySubstitution s a h k r).Splits :=
  (elementarySubstitution_isPFPolynomial_of_nonneg s a ha hh hk hkh hsize r hpar
    ).ne_zero_and_splits_of_eval_zero_ne_zero
    (elementarySubstitution_eval_zero_ne_zero s a ha hh hk hkh hsize r)

/-- Every root of a parity-compatible elementary-coordinate specialization is strictly
negative. -/
theorem roots_elementarySubstitution_neg :
    ∀ x ∈ (elementarySubstitution s a h k r).roots, x < 0 :=
  (elementarySubstitution_isPFPolynomial_of_nonneg s a ha hh hk hkh hsize r hpar
    ).roots_neg_of_eval_zero_ne_zero
    (elementarySubstitution_eval_zero_ne_zero s a ha hh hk hkh hsize r)

end RealRooted.Schur
