/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

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

end Matrix
