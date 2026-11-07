/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-! # Linearity and sign changes of weighted differential kernels -/

public section

namespace Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The weighted differential kernel is additive in its coefficient sequence. -/
theorem weightedDerivativeKernel_add (κ : R) (f g : ℕ → R) :
    weightedDerivativeKernel κ (f + g) =
      weightedDerivativeKernel κ f + weightedDerivativeKernel κ g := by
  ext i j
  by_cases h : j ≤ i + 1 <;> simp [weightedDerivativeKernel, h, mul_add]

/-- The weighted differential kernel respects coefficient subtraction. -/
theorem weightedDerivativeKernel_sub (κ : R) (f g : ℕ → R) :
    weightedDerivativeKernel κ (f - g) =
      weightedDerivativeKernel κ f - weightedDerivativeKernel κ g := by
  ext i j
  by_cases h : j ≤ i + 1 <;> simp [weightedDerivativeKernel, h, mul_sub]

/-- Scalar multiplication of the input scales the whole weighted kernel. -/
theorem weightedDerivativeKernel_smul (κ a : R) (f : ℕ → R) :
    weightedDerivativeKernel κ (a • f) = a • weightedDerivativeKernel κ f := by
  ext i j
  by_cases h : j ≤ i + 1
  · simp only [weightedDerivativeKernel, h, ite_true, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [weightedDerivativeKernel, h]

/-- Weighted differential kernels commute with change of coefficient ring. -/
theorem weightedDerivativeKernel_map (φ : R →+* S) (κ : R) (f : ℕ → R) :
    (weightedDerivativeKernel κ f).map φ =
      weightedDerivativeKernel (φ κ) (fun k ↦ φ (f k)) := by
  ext i j
  by_cases h : j ≤ i + 1 <;> simp [weightedDerivativeKernel, h]

/-- Reversing coefficient signs changes a finite weighted kernel to the
negative of its checkerboard conjugate. -/
theorem weightedDerivativeKernel_signed_fin (κ : R) (f : ℕ → R) (n : ℕ) :
    ((weightedDerivativeKernel κ (fun k ↦ (-1 : R) ^ k * f k)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) R) =
    -checkerboard ((weightedDerivativeKernel κ f).submatrix Fin.val Fin.val :
      Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : j.val ≤ i.val + 1
  · have hsign : (-1 : R) ^ (i.val + 1 - j.val) =
        -((-1 : R) ^ i.val * (-1 : R) ^ j.val) := by
      calc
        _ = ((-1 : R) ^ (i.val + 1 - j.val) * (-1 : R) ^ j.val) *
            (-1 : R) ^ j.val := by
          rw [mul_assoc, ← mul_pow]
          simp
        _ = (-1 : R) ^ (i.val + 1) * (-1 : R) ^ j.val := by
          rw [← pow_add, Nat.sub_add_cancel h]
        _ = _ := by rw [pow_succ]; ring
    simp only [Matrix.submatrix_apply, Matrix.neg_apply, checkerboard,
      weightedDerivativeKernel, h, ite_true]
    rw [hsign]
    ring
  · simp [Matrix.submatrix_apply, checkerboard, weightedDerivativeKernel, h]

end Matrix
