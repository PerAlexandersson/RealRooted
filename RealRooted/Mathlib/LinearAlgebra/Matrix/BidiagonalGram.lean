/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal

/-!
# First-coordinate decomposition of bidiagonal Gram matrices

Removing the first row and column of `B Bᵀ` for a lower-bidiagonal matrix
shifts the bidiagonal data and adds the square of the first subdiagonal
entry at the new first coordinate. These exact block identities explain
the adjacent sums and products in Stieltjes-to-Jacobi contraction.
-/

public section

open scoped BigOperators

namespace Matrix

variable {R : Type*} [CommRing R]

/-- Only the first diagonal entry is nonzero in the first bidiagonal row. -/
theorem lowerBidiagonalFin_zero (d s : ℕ → R) (n : ℕ) (j : Fin (n + 1)) :
    lowerBidiagonalFin (n + 1) d s 0 j = if j = 0 then d 0 else 0 := by
  simp [lowerBidiagonalFin_apply, eq_comm]

/-- The lower part of the first bidiagonal column has one possible nonzero entry. -/
theorem lowerBidiagonalFin_succ_zero (d s : ℕ → R) (n : ℕ) (i : Fin (n + 1)) :
    lowerBidiagonalFin (n + 2) d s i.succ 0 = if i = 0 then s 0 else 0 := by
  by_cases hi : i = 0
  · subst i
    simp [lowerBidiagonalFin_apply]
  · have hval : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [lowerBidiagonalFin_apply, hi, hval]

/-- The trailing principal bidiagonal block shifts both coefficient sequences. -/
theorem lowerBidiagonalFin_succ_succ (d s : ℕ → R) (n : ℕ) (i j : Fin n) :
    lowerBidiagonalFin (n + 1) d s i.succ j.succ =
      lowerBidiagonalFin n (fun k => d (k + 1)) (fun k => s (k + 1)) i j := by
  simp [lowerBidiagonalFin_apply]

/-- The first Gram diagonal entry is the square of the first bidiagonal entry. -/
theorem lowerBidiagonalFin_mul_transpose_zero_zero (d s : ℕ → R) (n : ℕ) :
    (lowerBidiagonalFin (n + 1) d s * (lowerBidiagonalFin (n + 1) d s)ᵀ) 0 0 =
      d 0 ^ 2 := by
  simp [Matrix.mul_apply, transpose_apply, pow_two]

/-- The first Gram off-diagonal row couples only to the next coordinate. -/
theorem lowerBidiagonalFin_mul_transpose_zero_succ
    (d s : ℕ → R) (n : ℕ) (i : Fin (n + 1)) :
    (lowerBidiagonalFin (n + 2) d s * (lowerBidiagonalFin (n + 2) d s)ᵀ) 0 i.succ =
      if i = 0 then d 0 * s 0 else 0 := by
  simp only [Matrix.mul_apply, transpose_apply, lowerBidiagonalFin_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [lowerBidiagonalFin_succ_zero]
  simp only [mul_ite, mul_zero]

/-- The first Gram off-diagonal column has the same single coupling. -/
theorem lowerBidiagonalFin_mul_transpose_succ_zero
    (d s : ℕ → R) (n : ℕ) (i : Fin (n + 1)) :
    (lowerBidiagonalFin (n + 2) d s * (lowerBidiagonalFin (n + 2) d s)ᵀ) i.succ 0 =
      if i = 0 then d 0 * s 0 else 0 := by
  simpa only [Matrix.mul_apply, transpose_apply, mul_comm] using
    lowerBidiagonalFin_mul_transpose_zero_succ d s n i

/-- The trailing Gram block is the shifted bidiagonal Gram matrix plus a
single nonnegative diagonal correction when the coefficient ring is ordered. -/
theorem lowerBidiagonalFin_mul_transpose_succ_succ
    (d s : ℕ → R) (n : ℕ) (i j : Fin (n + 1)) :
    (lowerBidiagonalFin (n + 2) d s * (lowerBidiagonalFin (n + 2) d s)ᵀ) i.succ j.succ =
      (lowerBidiagonalFin (n + 1) (fun k => d (k + 1)) (fun k => s (k + 1)) *
        (lowerBidiagonalFin (n + 1) (fun k => d (k + 1)) (fun k => s (k + 1)))ᵀ) i j +
      if i = 0 ∧ j = 0 then s 0 ^ 2 else 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [transpose_apply, lowerBidiagonalFin_succ_zero,
    lowerBidiagonalFin_succ_succ]
  rw [Matrix.mul_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [hi, hj, transpose_apply, pow_two, add_comm]

end Matrix
