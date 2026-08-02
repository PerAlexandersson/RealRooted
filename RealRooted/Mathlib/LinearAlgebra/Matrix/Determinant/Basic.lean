module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace Matrix
variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

-- TODO: Replace `det_zero`
@[simp] lemma det_zero' [Nonempty n] : (0 : Matrix n n R).det = 0 := det_zero ‹_›

/-- The alternating vector of maximal row-deletion minors of a rectangular matrix lies in the
kernel of its transpose. This is the Laplace expansion of the matrix obtained by adjoining a
duplicate of any chosen column. -/
theorem transpose_mulVec_alternating_det_submatrix_succAbove {q : ℕ}
    (B : Matrix (Fin (q + 1)) (Fin q) R) :
    B.transpose.mulVec (fun i => (-1 : R) ^ (i : ℕ) *
      (B.submatrix i.succAbove id).det) = 0 := by
  ext j
  let A : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
    fun i => Fin.cases (B i j) (B i)
  have hminor (i : Fin (q + 1)) :
      A.submatrix i.succAbove Fin.succ = B.submatrix i.succAbove id := rfl
  have hne : (0 : Fin (q + 1)) ≠ j.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  have hdet : A.det = 0 := det_zero_of_column_eq hne (by
    intro i
    rfl)
  rw [det_succ_column_zero] at hdet
  simp_rw [hminor] at hdet
  simpa [mulVec, dotProduct, A, mul_comm, mul_left_comm, mul_assoc] using hdet

/-- Expanding a matrix with constant first column after adjacent row subtraction. -/
theorem det_eq_det_adjacentRowDiff_of_firstColumn_eq_one {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : ∀ i, A i 0 = 1) :
    A.det =
      (Matrix.of fun (i j : Fin n) =>
        A i.succ j.succ - A i.castSucc j.succ).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun i j => Fin.cases (A 0 j)
      (fun k => A k.succ j - A k.castSucc j) i
  have hdet : A.det = B.det := by
    apply det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
    · intro j
      simp [B]
    · intro i j
      simp [B]
  rw [hdet, det_succ_column_zero, Fin.sum_univ_succ]
  simp [B, hA]
  apply congrArg det
  ext i j
  rfl

end Matrix
