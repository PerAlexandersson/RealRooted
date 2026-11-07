/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Determinants of positive affine matrix pencils -/

public section

open Polynomial

namespace Matrix

/-- The determinant of `I + X A` is the reversed characteristic polynomial
of `A`, composed with `-X`. -/
theorem det_one_add_X_smul_eq_reverse_charpoly_comp_neg_X
    {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) :
    det (1 + (X : R[X]) • A.map C) = A.charpoly.reverse.comp (-X) := by
  rw [reverse_charpoly, charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> simp

/-- The determinant of `X I + A` is the characteristic polynomial of `-A`. -/
theorem det_X_smul_one_add_map_eq_charpoly_neg
    {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) :
    det ((X : R[X]) • (1 : Matrix n n R[X]) + A.map C) = (-A).charpoly := by
  rw [charpoly, charmatrix]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- An affine determinant pencil factors through a right inverse; cyclically
moving its last matrix factor gives a second normalized representation. -/
theorem det_map_add_X_smul_of_mul_eq_one
    {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M B L S : Matrix n n R) (hMB : M * B = 1) :
    det (M.map C + (X : R[X]) • (S * L * S).map C) =
      C M.det * det (1 + (X : R[X]) • (S * B * S * L).map C) := by
  have hmul :
      M.map C * (1 + (X : R[X]) • (B * S * L * S).map C) =
        M.map C + (X : R[X]) • (S * L * S).map C := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.map_mul]
    congr 2
    simp only [← Matrix.mul_assoc, hMB, Matrix.one_mul]
  have hrotate :
      det (1 + (X : R[X]) • (B * S * L * S).map C) =
        det (1 + (X : R[X]) • (S * B * S * L).map C) := by
    simpa only [Matrix.map_mul, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul] using
      det_one_add_mul_comm ((X : R[X]) • (B * S * L).map C) (S.map C)
  rw [← hmul, Matrix.det_mul, hrotate]
  congr 1
  exact (C.map_det M).symm

/-- Factoring the variable coefficient of an affine determinant pencil gives
an ordinary characteristic-polynomial pencil. -/
theorem det_map_add_X_smul_eq_det_mul_of_mul_eq_one
    {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M A B : Matrix n n R) (hAB : A * B = 1) :
    det (M.map C + (X : R[X]) • A.map C) =
      C A.det * det ((X : R[X]) • (1 : Matrix n n R[X]) + (B * M).map C) := by
  have hmul :
      A.map C * ((X : R[X]) • (1 : Matrix n n R[X]) + (B * M).map C) =
        M.map C + (X : R[X]) • A.map C := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← Matrix.map_mul]
    have hcancel : A * (B * M) = M := by
      rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hcancel, add_comm]
  rw [← hmul, Matrix.det_mul]
  congr 1
  exact (C.map_det A).symm


/-- Reflection of a characteristic polynomial gives the positive affine
matrix pencil, up to the usual dimension-dependent sign. -/
theorem det_X_smul_one_add_map_eq_C_mul_charpoly_comp_neg_X
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) :
    det ((X : R[X]) • (1 : Matrix ι ι R[X]) + A.map C) =
      C ((-1 : R) ^ Fintype.card ι) * A.charpoly.comp (-X) := by
  symm
  rw [charpoly, ← coe_compRingHom_apply, RingHom.map_det,
    C_pow, C_neg, C_1, ← Matrix.det_smul]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [charmatrix, add_comm]
  · simp [charmatrix, hij]


end Matrix
