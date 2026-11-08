module

public import RealRooted.Schur.ElementaryToeplitz
public import RealRooted.TotallyNonnegPencil.CornerInterlacing
import RealRooted.TotallyNonnegPencil.Checkerboard
import RealRooted.Schur.Interlacing
import RealRooted.Schur.ElementaryPositivity
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-! # Signed elementary-coordinate deformations of rectangular elementary determinants -/

@[expose] public section

open Matrix Polynomial

namespace RealRooted.Schur

/-- The rectangular elementary-coordinate deformation in the sign convention
`e_j ↦ e_j + (-1)^(j-r) t`. The equivalent checkerboard determinant makes sense
for every coordinate, including those beyond the alphabet size. -/
noncomputable def rectangularElementarySubstitution {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (r j n : ℕ) : ℝ[X] :=
  checkerboardPencil (elementaryMatrix s a (fun _ : Fin n => r) (fun _ => 0))
    (activeMatrix (fun i => (columnIndex (fun _ : Fin n => r) i : ℤ))
      (fun i => (columnIndex (fun _ : Fin n => 0) i : ℤ)) j)

/-- On a rectangular active diagonal the checkerboard sign is constant. -/
theorem checkerboard_activeMatrix_rectangular (r j n : ℕ) :
    checkerboard (activeMatrix (fun i => (columnIndex (fun _ : Fin n => r) i : ℤ))
      (fun i => (columnIndex (fun _ : Fin n => 0) i : ℤ)) j) =
    (-1 : ℝ) ^ (r + j) • activeMatrix
      (fun i => (columnIndex (fun _ : Fin n => r) i : ℤ))
      (fun i => (columnIndex (fun _ : Fin n => 0) i : ℤ)) j := by
  apply activeMatrix_checkerboard_of_sign
  intro p q hactive
  have hp := p.isLt
  have hq := q.isLt
  have hrel : r + q.val = j + p.val := by
    dsimp [columnIndex] at hactive
    lia
  apply neg_one_pow_congr
  simp only [Nat.even_iff]
  lia

/-- The checkerboard definition is exactly substitution of the signed moving
coordinate in the elementary Jacobi–Trudi determinant. The exponent `r+j`
has the same parity as the integer exponent `j-r`. -/
theorem rectangularElementarySubstitution_eq_det {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (r j n : ℕ) :
    rectangularElementarySubstitution s a r j n =
      det ((elementaryMatrix s a (fun _ : Fin n => r) (fun _ => 0)).map C +
        (X : ℝ[X]) • ((-1 : ℝ) ^ (r + j) • activeMatrix
          (fun i => (columnIndex (fun _ : Fin n => r) i : ℤ))
          (fun i => (columnIndex (fun _ : Fin n => 0) i : ℤ)) j).map C) := by
  simp only [rectangularElementarySubstitution, checkerboardPencil,
    checkerboard_activeMatrix_rectangular]

/-- At zero the signed deformation is the ordinary rectangular determinant. -/
@[simp] theorem rectangularElementarySubstitution_eval_zero {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (r j n : ℕ) :
    (rectangularElementarySubstitution s a r j n).eval 0 =
      (elementaryMatrix s a (fun _ : Fin n => r) (fun _ => 0)).det := by
  simp [rectangularElementarySubstitution]

variable {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
  (r j : ℕ) (hsize : r ≤ (s.filter fun i => 0 < a i).card)

include ha hsize

/-- The rectangular elementary Jacobi–Trudi matrix has positive determinant. -/
private theorem det_elementaryMatrix_rectangular_pos (n : ℕ) :
    0 < (elementaryMatrix s a (fun _ : Fin n => r) (fun _ => 0)).det :=
  det_elementaryMatrix_pos_of_nonneg s a ha antitone_const antitone_const
    (fun _ => Nat.zero_le _) (fun _ => by simpa only [Nat.zero_add] using hsize)

/-- All signed rectangular elementary-coordinate deformations are PF polynomials. -/
theorem rectangularElementarySubstitution_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (rectangularElementarySubstitution s a r j n) :=
  (elementaryMatrix_isTotallyNonneg s a ha (antitone_const : Antitone fun _ : Fin n => r)
    (antitone_const : Antitone fun _ : Fin n => (0 : ℕ))
    ).isPFPolynomial_det_map_add_X_smul_checkerboard
    (activeMatrix_columnIndex_isTotallyNonneg antitone_const antitone_const j)
    (det_elementaryMatrix_rectangular_pos s a ha r hsize n)

/-- The signed rectangular specialization has nonzero constant term. -/
private theorem rectangularElementarySubstitution_eval_zero_ne_zero (n : ℕ) :
    (rectangularElementarySubstitution s a r j n).eval 0 ≠ 0 := by
  rw [rectangularElementarySubstitution_eval_zero]
  exact (det_elementaryMatrix_rectangular_pos s a ha r hsize n).ne'

/-- The signed rectangular specialization is nonzero and splits over the reals. -/
theorem rectangularElementarySubstitution_isRealRooted (n : ℕ) :
    rectangularElementarySubstitution s a r j n ≠ 0 ∧
      (rectangularElementarySubstitution s a r j n).Splits :=
  (rectangularElementarySubstitution_isPFPolynomial s a ha r j hsize n
    ).ne_zero_and_splits_of_eval_zero_ne_zero
    (rectangularElementarySubstitution_eval_zero_ne_zero s a ha r j hsize n)

/-- Every finite root of a signed rectangular elementary-coordinate deformation is negative. -/
theorem roots_rectangularElementarySubstitution_neg (n : ℕ) :
    ∀ x ∈ (rectangularElementarySubstitution s a r j n).roots, x < 0 :=
  (rectangularElementarySubstitution_isPFPolynomial s a ha r j hsize n
    ).roots_neg_of_eval_zero_ne_zero
    (rectangularElementarySubstitution_eval_zero_ne_zero s a ha r j hsize n)

/-- Consecutive widths of every rectangular elementary-coordinate deformation interlace.
No parity restriction on the height or the moving coordinate is needed. -/
theorem strictInterl_rectangularElementarySubstitution (n : ℕ) :
    StrictInterl (rectangularElementarySubstitution s a r j n)
      (rectangularElementarySubstitution s a r j (n + 1)) := by
  have hM := elementaryMatrix_isTotallyNonneg s a ha
    (antitone_const : Antitone (fun _ : Fin (n + 1) => r))
    (antitone_const : Antitone (fun _ : Fin (n + 1) => (0 : ℕ)))
  have hd := det_elementaryMatrix_rectangular_pos s a ha r hsize (n + 1)
  have hs := det_elementaryMatrix_rectangular_pos s a ha r hsize n
  simpa only [rectangularElementarySubstitution, elementaryMatrix_submatrix_succ,
    activeMatrix_columnIndex_submatrix_succ, Function.comp_def]
    using hM.strictInterl_checkerboardPencil_succ
      (activeMatrix_columnIndex_isTotallyNonneg antitone_const antitone_const j) hd
      (by simpa only [elementaryMatrix_submatrix_succ, Function.comp_def] using hs)

end RealRooted.Schur
