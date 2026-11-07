/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

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

end Matrix
