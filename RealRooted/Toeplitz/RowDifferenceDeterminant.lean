module

import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a matrix with constant upper-triangular columns

Let `B` be a square matrix over a commutative ring such that `B i j = B j j` for `i ≤ j`, that
is, every column is constant down to its diagonal entry. Subtracting each row from the one above
it (a unimodular operation) leaves a lower triangular matrix, whose diagonal entries are
`B i i - B (i + 1) i` and `B n n`. Hence
`det B = B n n * ∏ i < n, (B i i - B (i + 1) i)`.
-/

public section

open Matrix

namespace RealRooted

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The unipotent matrix subtracting from each row the next one: row `i < n` becomes
`row i - row (i + 1)`, and the last row is unchanged. -/
def rowDifference (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i k =>
    Fin.lastCases (motive := fun _ => R) (if k = Fin.last n then 1 else 0)
      (fun i' => (if k = i'.castSucc then 1 else 0) - (if k = i'.succ then 1 else 0)) i

lemma rowDifference_mul_castSucc (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin n)
    (j : Fin (n + 1)) :
    (rowDifference R n * B) i.castSucc j = B i.castSucc j - B i.succ j := by
  simp [rowDifference, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib]

lemma rowDifference_mul_last (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (j : Fin (n + 1)) :
    (rowDifference R n * B) (Fin.last n) j = B (Fin.last n) j := by
  simp [rowDifference, Matrix.mul_apply]

lemma det_rowDifference : (rowDifference R n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    induction i using Fin.lastCases with
    | last => simp [rowDifference]
    | cast i => simp [rowDifference, (Fin.castSucc_lt_succ).ne]
  · intro i k hki
    induction i using Fin.lastCases with
    | last =>
      have : k ≠ Fin.last n := ne_of_lt hki
      simp [rowDifference, this]
    | cast i =>
      have h1 : k ≠ i.castSucc := hki.ne
      have h2 : k ≠ i.succ := (hki.trans Fin.castSucc_lt_succ).ne
      simp [rowDifference, h1, h2]

/-- **Determinant of a matrix with constant upper-triangular columns.** If `B i j = B j j` for
`i ≤ j`, then `det B = B n n * ∏ i < n, (B i i - B (i + 1) i)`. -/
theorem det_eq_last_mul_prod_of_forall_le {B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hB : ∀ ⦃i j : Fin (n + 1)⦄, i ≤ j → B i j = B j j) :
    B.det = B (Fin.last n) (Fin.last n) *
      ∏ i : Fin n, (B i.castSucc i.castSucc - B i.succ i.castSucc) := by
  have hdet : (rowDifference R n * B).det = B.det := by
    rw [Matrix.det_mul, det_rowDifference, one_mul]
  rw [← hdet, Matrix.det_of_isLowerTriangular, Fin.prod_univ_castSucc, mul_comm]
  · simp only [rowDifference_mul_castSucc, rowDifference_mul_last]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    induction i using Fin.lastCases with
    | last => exact absurd hij' (not_lt.mpr (Fin.le_last j))
    | cast i =>
      have h1 : i.castSucc ≤ j := hij'.le
      have h2 : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hij'
      simp [rowDifference_mul_castSucc, hB h1, hB h2]

end RealRooted
