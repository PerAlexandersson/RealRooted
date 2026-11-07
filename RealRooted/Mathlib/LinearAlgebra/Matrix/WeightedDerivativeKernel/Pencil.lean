/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel.Algebra
import Mathlib.Tactic.Ring

/-! # The affine polynomial pencil of a signed weighted kernel -/

public section

open Polynomial

namespace Matrix

/-- The signed weighted kernel of the formal denominator `q - X b` is an
affine pencil with checkerboard signs on its variable part. -/
theorem weightedDerivativeKernel_signed_sub_X_mul (R : Type*) [CommRing R]
    (κ : R) (q b : ℕ → R) (n : ℕ) :
    ((weightedDerivativeKernel (C κ)
      (fun k ↦ (-1 : R[X]) ^ k * (C (q k) - X * C (b k)))).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) R[X]) =
    (((weightedDerivativeKernel κ (fun k ↦ (-1 : R) ^ k * q k)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) R).map C) +
    (X : R[X]) • (checkerboard
      ((weightedDerivativeKernel κ b).submatrix Fin.val Fin.val :
        Matrix (Fin n) (Fin n) R)).map C := by
  let f : ℕ → R[X] := fun k ↦ C ((-1 : R) ^ k * q k)
  let g : ℕ → R[X] := fun k ↦ C ((-1 : R) ^ k * b k)
  have hseq :
      (fun k ↦ (-1 : R[X]) ^ k * (C (q k) - X * C (b k))) = f - (X : R[X]) • g := by
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, f, g, map_mul,
      map_pow, map_neg, map_one]
    ring
  rw [hseq, weightedDerivativeKernel_sub, weightedDerivativeKernel_smul]
  change
    ((weightedDerivativeKernel (C κ) f).submatrix Fin.val Fin.val :
      Matrix (Fin n) (Fin n) R[X]) -
    (X : R[X]) • ((weightedDerivativeKernel (C κ) g).submatrix Fin.val Fin.val :
      Matrix (Fin n) (Fin n) R[X]) = _
  have hf :
      ((weightedDerivativeKernel (C κ) f).submatrix Fin.val Fin.val :
        Matrix (Fin n) (Fin n) R[X]) =
      (((weightedDerivativeKernel κ (fun k ↦ (-1 : R) ^ k * q k)).submatrix
        Fin.val Fin.val : Matrix (Fin n) (Fin n) R).map C) := by
    exact congrArg (fun A : Matrix ℕ ℕ R[X] ↦
      (A.submatrix Fin.val Fin.val : Matrix (Fin n) (Fin n) R[X]))
      (weightedDerivativeKernel_map C κ (fun k ↦ (-1 : R) ^ k * q k)).symm
  have hg :
      ((weightedDerivativeKernel (C κ) g).submatrix Fin.val Fin.val :
        Matrix (Fin n) (Fin n) R[X]) =
      (((weightedDerivativeKernel κ (fun k ↦ (-1 : R) ^ k * b k)).submatrix
        Fin.val Fin.val : Matrix (Fin n) (Fin n) R).map C) := by
    exact congrArg (fun A : Matrix ℕ ℕ R[X] ↦
      (A.submatrix Fin.val Fin.val : Matrix (Fin n) (Fin n) R[X]))
      (weightedDerivativeKernel_map C κ (fun k ↦ (-1 : R) ^ k * b k)).symm
  rw [hf, hg, weightedDerivativeKernel_signed_fin κ b n]
  apply Matrix.ext
  intro i j
  simp

end Matrix
