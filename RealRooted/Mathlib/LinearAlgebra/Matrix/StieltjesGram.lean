/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal
import RealRooted.Mathlib.LinearAlgebra.Matrix.BidiagonalGram
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real

/-!
# Finite positive Jacobi matrices from Stieltjes numerators

The lower bidiagonal matrix with diagonal `sqrt (a (2*i))` and subdiagonal
`sqrt (a (2*i+1))` gives a positive semidefinite Gram matrix. A nonnegative
correction at its first diagonal entry is preserved by taking trailing
principal blocks. Zero coefficients and singular matrices are allowed.
-/

public section

namespace Matrix

/-- The finite Jacobi Gram matrix with an optional first-diagonal correction. -/
@[expose] noncomputable def stieltjesJacobiMatrix (a : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  let B := lowerBidiagonalFin (n + 1)
    (fun i => Real.sqrt (a (2 * i))) (fun i => Real.sqrt (a (2 * i + 1)))
  B * Bᵀ + diagonal (fun i => if i = 0 then c else 0)

/-- A nonnegative first-diagonal correction keeps the Jacobi Gram matrix positive
semidefinite. The square-root definition makes this true for arbitrary `a`. -/
theorem posSemidef_stieltjesJacobiMatrix (a : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    (stieltjesJacobiMatrix a c n).PosSemidef := by
  apply PosSemidef.add
  · simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_self_mul_conjTranspose
        (lowerBidiagonalFin (n + 1) (fun i => Real.sqrt (a (2 * i)))
          (fun i => Real.sqrt (a (2 * i + 1))))
  · apply PosSemidef.diagonal
    intro i
    change 0 ≤ if i = 0 then c else 0
    split_ifs <;> positivity

/-- The first diagonal coefficient is the first Stieltjes numerator plus the correction. -/
theorem stieltjesJacobiMatrix_zero_zero (a : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (ha : 0 ≤ a 0) : stieltjesJacobiMatrix a c n 0 0 = c + a 0 := by
  dsimp only [stieltjesJacobiMatrix]
  rw [Matrix.add_apply, lowerBidiagonalFin_mul_transpose_zero_zero, diagonal_apply_eq]
  simp [Real.sq_sqrt ha, add_comm]

/-- The first row has only one off-diagonal coupling. -/
theorem stieltjesJacobiMatrix_zero_succ (a : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (i : Fin (n + 1)) :
    stieltjesJacobiMatrix a c (n + 1) 0 i.succ =
      if i = 0 then Real.sqrt (a 0) * Real.sqrt (a 1) else 0 := by
  dsimp only [stieltjesJacobiMatrix]
  rw [Matrix.add_apply, lowerBidiagonalFin_mul_transpose_zero_succ]
  simp [eq_comm]

/-- The first column has the same single off-diagonal coupling. -/
theorem stieltjesJacobiMatrix_succ_zero (a : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (i : Fin (n + 1)) :
    stieltjesJacobiMatrix a c (n + 1) i.succ 0 =
      if i = 0 then Real.sqrt (a 0) * Real.sqrt (a 1) else 0 := by
  dsimp only [stieltjesJacobiMatrix]
  rw [Matrix.add_apply, lowerBidiagonalFin_mul_transpose_succ_zero]
  simp

/-- Removing the first coordinate shifts the numerator data by two; the next
Stieltjes numerator becomes the new first-diagonal correction. -/
theorem stieltjesJacobiMatrix_submatrix_succ (a : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (ha : 0 ≤ a 1) :
    (stieltjesJacobiMatrix a c (n + 1)).submatrix Fin.succ Fin.succ =
      stieltjesJacobiMatrix (fun k => a (k + 2)) (a 1) n := by
  have hd : (fun k => Real.sqrt (a (2 * (k + 1)))) =
      (fun k => Real.sqrt (a (2 * k + 2))) := by
    funext k
    congr 2
  have hs : (fun k => Real.sqrt (a (2 * (k + 1) + 1))) =
      (fun k => Real.sqrt (a (2 * k + 1 + 2))) := by
    funext k
    congr 2
  ext i j
  dsimp only [submatrix_apply, stieltjesJacobiMatrix]
  rw [Matrix.add_apply, lowerBidiagonalFin_mul_transpose_succ_succ, Matrix.add_apply]
  simp only [hd, hs, Nat.mul_zero, Nat.zero_add, Real.sq_sqrt ha]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;> simp [hi]
  · simp [hij, Fin.succ_inj]
    aesop

end Matrix
