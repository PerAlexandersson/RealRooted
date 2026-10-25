/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.DesnanotJacobi

/-!
# Ordered deleted-column Plücker identity

The relation is obtained from the Desnanot--Jacobi identity after adjoining a
standard-basis row.  Laplace expansion of the four resulting minors gives the
three maximal minors in the Plücker relation.
-/

@[expose] public section

namespace Matrix

private def prependRow {R : Type*} {n : ℕ}
    (v : Fin (n + 1) → R) (M : Matrix (Fin n) (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i ↦ Fin.cases v M i

private theorem det_prependRow_single
    {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) R) (j : Fin (n + 1)) :
    (prependRow (fun k ↦ if k = j then 1 else 0) M).det =
      (-1 : R) ^ (j : ℕ) * (M.submatrix id j.succAbove).det := by
  classical
  rw [Matrix.det_succ_row_zero]
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro k _ hkj
    have hzero : prependRow (fun k ↦ if k = j then 1 else 0) M 0 k = 0 := by
      change (if k = j then 1 else 0) = 0
      simp [hkj]
    rw [hzero, mul_zero, zero_mul]
  · simp
  · have hone : prependRow (fun k ↦ if k = j then 1 else 0) M 0 j = 1 := by
      change (if j = j then 1 else 0) = 1
      simp
    rw [hone, mul_one]
    rfl

private theorem det_prependRow_single_castSucc
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let k : Fin (q + 3) := b.castSucc.succ
    let A := prependRow (fun j ↦ if j = k then 1 else 0) M
    (A.submatrix Fin.castSucc Fin.castSucc).det =
      (-1 : R) ^ ((b : ℕ) + 1) *
        (M.submatrix Fin.castSucc
          (fun j ↦ (b.succ.succAbove j).castSucc)).det := by
  classical
  dsimp
  let N := M.submatrix Fin.castSucc Fin.castSucc
  have hmatrix :
      (prependRow (fun j ↦ if j = b.castSucc.succ then 1 else 0) M).submatrix
          Fin.castSucc Fin.castSucc =
        prependRow (fun j : Fin (q + 2) ↦ if j = b.succ then 1 else 0) N := by
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · change (if j.castSucc = b.castSucc.succ then 1 else 0) =
        if j = b.succ then 1 else 0
      simp [Fin.ext_iff]
    · rfl
  rw [hmatrix, det_prependRow_single]
  congr 1

private theorem det_prependRow_single_succ
    {R : Type*} [CommRing R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let k : Fin (q + 3) := b.castSucc.succ
    let A := prependRow (fun j ↦ if j = k then 1 else 0) M
    (A.submatrix Fin.castSucc Fin.succ).det =
      (-1 : R) ^ (b : ℕ) *
        (M.submatrix Fin.castSucc
          (fun j ↦ (b.castSucc.succAbove j).succ)).det := by
  classical
  dsimp
  let N := M.submatrix Fin.castSucc Fin.succ
  have hmatrix :
      (prependRow (fun j ↦ if j = b.castSucc.succ then 1 else 0) M).submatrix
          Fin.castSucc Fin.succ =
        prependRow (fun j : Fin (q + 2) ↦ if j = b.castSucc then 1 else 0) N := by
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · change (if j.succ = b.castSucc.succ then 1 else 0) =
        if j = b.castSucc then 1 else 0
      simp [Fin.ext_iff]
    · rfl
  rw [hmatrix, det_prependRow_single]
  congr 1

/-- The canonical deleted-column Plücker relation for a rectangular matrix.

The nonzero middle minor is retained in the statement for compatibility with
the original bordered-determinant proof. -/
theorem det_ordered_delete_column_plucker
    {R : Type*} [Field R] {q : ℕ}
    (M : Matrix (Fin (q + 2)) (Fin (q + 3)) R) (b : Fin (q + 1)) :
    let d : Fin (q + 3) → R := fun j ↦ (M.submatrix id j.succAbove).det
    let deltaAC := (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) ↦ j.castSucc.succ)).det
    let deltaAB := (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) ↦ (b.castSucc.succAbove j).succ)).det
    let deltaBC := (M.submatrix Fin.castSucc
      (fun j : Fin (q + 1) ↦ (b.succ.succAbove j).castSucc)).det
    d b.castSucc.succ * deltaAC =
      d (Fin.last (q + 2)) * deltaAB + d 0 * deltaBC := by
  classical
  dsimp
  let k : Fin (q + 3) := b.castSucc.succ
  let A := prependRow (fun j ↦ if j = k then 1 else 0) M
  have h := det_mul_det_interior (n := q + 1) A
  have hA : A.det = (-1 : R) ^ ((b : ℕ) + 1) *
      (M.submatrix id b.castSucc.succ.succAbove).det := by
    simpa [A, k] using det_prependRow_single M k
  have hInterior :
      (A.submatrix (fun i : Fin (q + 1) ↦ i.castSucc.succ)
        (fun i : Fin (q + 1) ↦ i.castSucc.succ)).det =
        (M.submatrix Fin.castSucc
          (fun i : Fin (q + 1) ↦ i.castSucc.succ)).det := by
    congr 1
  have h00 : (A.submatrix Fin.succ Fin.succ).det =
      (M.submatrix id Fin.succ).det := by
    congr 1
  have h01 : (A.submatrix Fin.succ Fin.castSucc).det =
      (M.submatrix id Fin.castSucc).det := by
    congr 1
  rw [hA, hInterior, h00, h01,
    det_prependRow_single_castSucc M b, det_prependRow_single_succ M b] at h
  have hs : (-1 : R) ^ ((b : ℕ) + 1) = -(-1 : R) ^ (b : ℕ) := by
    rw [pow_succ]
    ring
  rw [hs] at h
  apply mul_left_cancel₀ (a := -(-1 : R) ^ (b : ℕ)) (by simp)
  calc
    -(-1 : R) ^ (b : ℕ) *
          ((M.submatrix id b.castSucc.succ.succAbove).det *
            (M.submatrix Fin.castSucc
              (fun j : Fin (q + 1) ↦ j.castSucc.succ)).det) =
        (-(-1 : R) ^ (b : ℕ) *
          (M.submatrix id b.castSucc.succ.succAbove).det) *
            (M.submatrix Fin.castSucc
              (fun j : Fin (q + 1) ↦ j.castSucc.succ)).det := by ring
    _ = (M.submatrix id Fin.succ).det *
          (-(-1 : R) ^ (b : ℕ) *
            (M.submatrix Fin.castSucc
              (fun j ↦ (b.succ.succAbove j).castSucc)).det) -
        (M.submatrix id Fin.castSucc).det *
          ((-1 : R) ^ (b : ℕ) *
            (M.submatrix Fin.castSucc
              (fun j ↦ (b.castSucc.succAbove j).succ)).det) := h
    _ = -(-1 : R) ^ (b : ℕ) *
        ((M.submatrix id (Fin.last (q + 2)).succAbove).det *
            (M.submatrix Fin.castSucc
              (fun j ↦ (b.castSucc.succAbove j).succ)).det +
          (M.submatrix id (0 : Fin (q + 3)).succAbove).det *
            (M.submatrix Fin.castSucc
              (fun j ↦ (b.succ.succAbove j).castSucc)).det) := by
      have hzero :
          (M.submatrix id (0 : Fin (q + 3)).succAbove).det =
            (M.submatrix id Fin.succ).det := by
        congr 1
      rw [Fin.succAbove_last, hzero]
      ring

end Matrix
