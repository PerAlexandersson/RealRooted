import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant-preserving adjacent column differences

This file packages the simultaneous finite column operation used to compare
Toeplitz minors before and after a causal forward difference.
-/

namespace Matrix

/-- Replace every nonterminal column by itself minus its successor, retaining
the terminal column. -/
def columnDifference {R : Type*} [AddGroup R] {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i j => Fin.lastCases (A i (Fin.last N))
    (fun j => A i j.castSucc - A i j.succ) j

/-- Simultaneous adjacent column differences preserve the determinant. -/
theorem det_columnDifference {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    (columnDifference A).det = A.det := by
  have hdet := det_eq_of_forall_col_eq_smul_add_pred
    (A := A.submatrix Fin.revPerm Fin.revPerm)
    (B := (columnDifference A).submatrix Fin.revPerm Fin.revPerm)
    (fun _ => (1 : R))
    (by
      intro i
      simp [columnDifference])
    (by
      intro i j
      change A i.rev j.succ.rev =
        columnDifference A i.rev j.succ.rev + 1 * A i.rev j.castSucc.rev
      rw [Fin.rev_succ, Fin.rev_castSucc]
      simp [columnDifference])
  simpa using hdet.symm

end Matrix
