import Mathlib

/-!
# Determinants of tridiagonal Toeplitz matrices

This file records the classical three-term recurrence for determinants of
tridiagonal Toeplitz matrices.
-/

namespace RealRooted

open Matrix

/-- The `n × n` tridiagonal Toeplitz matrix with diagonal `d`, superdiagonal
`s`, and subdiagonal `b`. -/
def tridiagM (d s b : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = (j : ℕ) then d
    else if (j : ℕ) = (i : ℕ) + 1 then s
    else if (i : ℕ) = (j : ℕ) + 1 then b
    else 0

@[simp]
lemma tridiagM_apply (d s b : ℝ) (n : ℕ) (i j : Fin n) :
    tridiagM d s b n i j =
      if (i : ℕ) = (j : ℕ) then d
      else if (j : ℕ) = (i : ℕ) + 1 then s
      else if (i : ℕ) = (j : ℕ) + 1 then b
      else 0 :=
  rfl

lemma tridiagM_det_zero (d s b : ℝ) :
    (tridiagM d s b 0).det = 1 := by
  simp

lemma tridiagM_det_one (d s b : ℝ) :
    (tridiagM d s b 1).det = d := by
  simp

/-- The classical three-term recurrence for tridiagonal Toeplitz determinants:
`D (n + 2) = d * D (n + 1) - s * b * D n`. -/
lemma tridiagM_det_rec (d s b : ℝ) (n : ℕ) :
    (tridiagM d s b (n + 2)).det =
      d * (tridiagM d s b (n + 1)).det - s * b * (tridiagM d s b n).det := by
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  ring_nf!
  simp [Matrix.submatrix]
  ring!

end RealRooted
