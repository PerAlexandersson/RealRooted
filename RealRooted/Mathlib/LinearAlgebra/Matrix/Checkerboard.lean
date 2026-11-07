/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! # Checkerboard signs on matrices -/

@[expose] public section

namespace Matrix

/-- Multiply each matrix entry by its row and column alternating signs. -/
def checkerboard {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ (-1 : R) ^ i.val * ((-1 : R) ^ j.val * A i j)

/-- Checkerboard signs are multiplication by diagonal sign matrices on each side. -/
theorem checkerboard_eq_diagonal_mul {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    checkerboard A = diagonal (fun i : Fin n ↦ (-1 : R) ^ i.val) * A *
      diagonal (fun i : Fin n ↦ (-1 : R) ^ i.val) := by
  ext i j
  simp only [checkerboard, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- Checkerboard signs preserve the identity matrix. -/
@[simp] theorem checkerboard_one {R : Type*} [CommRing R] {n : ℕ} :
    checkerboard (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [checkerboard, ← mul_pow]
  · simp [checkerboard, hij]

/-- Checkerboard conjugation preserves products. -/
theorem checkerboard_mul {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) :
    checkerboard (A * B) = checkerboard A * checkerboard B := by
  ext i j
  simp only [checkerboard, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : ((-1 : R) ^ k.val) * ((-1 : R) ^ k.val) = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = (-1 : R) ^ i.val * ((-1 : R) ^ j.val * (A i k * B k j)) *
        (((-1 : R) ^ k.val) * ((-1 : R) ^ k.val)) := by rw [hk, mul_one]
    _ = _ := by ring

/-- Leading sections commute with checkerboard signs. -/
@[simp] theorem checkerboard_submatrix_castSucc {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (checkerboard A).submatrix Fin.castSucc Fin.castSucc =
      checkerboard (A.submatrix Fin.castSucc Fin.castSucc) := by
  rfl

end Matrix
