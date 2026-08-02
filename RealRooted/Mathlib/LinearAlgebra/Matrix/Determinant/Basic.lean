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

end Matrix
