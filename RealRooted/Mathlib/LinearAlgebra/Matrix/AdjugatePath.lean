import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Logic.Equiv.Fin.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.Submatrix

/-!
# Recursive cofactor expansion for matrix paths

This file records the one-step Laplace expansion which recursively exposes an
off-diagonal adjugate entry as a first edge followed by an adjugate entry of the
principal submatrix with the initial vertex deleted.  Iterating this identity
is the simple-path/cofactor expansion.
-/

open scoped BigOperators
open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R]

/-- Expanding an off-diagonal adjugate entry from vertex `0` along its first
row gives a weighted adjugate entry of the principal submatrix deleting `0`.
The minus sign is cancelled by the off-diagonal entries of a characteristic
matrix. -/
theorem adjugate_zero_succ {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (j : Fin (n + 1)) :
    adjugate A 0 j.succ =
      -∑ k : Fin (n + 1), A 0 k.succ *
        adjugate (A.submatrix Fin.succ Fin.succ) k j := by
  rw [adjugate_fin_succ_eq_det_submatrix, det_succ_row_zero]
  simp only [Fin.val_zero, add_zero, Fin.val_succ, Matrix.submatrix_apply,
    Fin.succ_succAbove_zero, Fin.zero_succAbove]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [adjugate_fin_succ_eq_det_submatrix]
  have hminor :
      ((A.submatrix j.succ.succAbove (Fin.succAbove 0)).submatrix
          Fin.succ k.succAbove).det =
        ((A.submatrix Fin.succ Fin.succ).submatrix
          j.succAbove k.succAbove).det := by
    congr 1
    ext a b
    simp
  rw [hminor]
  rw [pow_succ', pow_add]
  ring

/-- For a characteristic matrix the preceding cofactor expansion has positive
edge weights: each off-diagonal entry contributes `-C (A 0 k.succ)`, which
cancels the cofactor sign. -/
theorem adjugate_charmatrix_zero_succ {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (j : Fin (n + 1)) :
    adjugate A.charmatrix 0 j.succ =
      ∑ k : Fin (n + 1), C (A 0 k.succ) *
        adjugate (A.submatrix Fin.succ Fin.succ).charmatrix k j := by
  rw [adjugate_zero_succ]
  rw [charmatrix_submatrix_self A Fin.succ (Fin.succ_injective (n + 1))]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [charmatrix_apply_ne A 0 k.succ (Fin.ne_of_lt (Fin.succ_pos k))]
  ring

/-- Coordinate-free-in-`Fin` form of `adjugate_zero_succ`: delete an arbitrary
initial vertex `i`, and address every possible next vertex using
`i.succAbove`. -/
theorem adjugate_apply_succAbove {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    adjugate A i (i.succAbove j) =
      -∑ k : Fin (n + 1), A i (i.succAbove k) *
        adjugate (A.submatrix i.succAbove i.succAbove) k j := by
  let e : Fin (n + 2) ≃ Fin (n + 2) :=
    (finSuccEquiv (n + 1)).trans (finSuccEquiv' i).symm
  have h := adjugate_zero_succ (A.submatrix e e) j
  have he : e ∘ Fin.succ = i.succAbove := by
    funext k
    simp [e]
  simpa only [adjugate_submatrix_equiv_self, Matrix.submatrix_apply,
    Matrix.submatrix_submatrix, Function.comp_apply, he, e, Equiv.trans_apply,
    finSuccEquiv_zero, finSuccEquiv_succ, finSuccEquiv'_symm_none,
    finSuccEquiv'_symm_some] using h

/-- The arbitrary-initial-vertex characteristic-matrix recurrence.  This is
the one-step form of the positive simple-path/cofactor expansion. -/
theorem adjugate_charmatrix_apply_succAbove {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    adjugate A.charmatrix i (i.succAbove j) =
      ∑ k : Fin (n + 1), C (A i (i.succAbove k)) *
        adjugate (A.submatrix i.succAbove i.succAbove).charmatrix k j := by
  rw [adjugate_apply_succAbove]
  rw [charmatrix_submatrix_self A i.succAbove i.succAbove_right_injective]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [charmatrix_apply_ne A i (i.succAbove k) (Fin.succAbove_ne i k).symm]
  ring

end Matrix
