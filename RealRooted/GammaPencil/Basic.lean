/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.HomogeneousOre

/-!
# The gamma pencil: elementary operator algebra

This file defines the first-order operator governing the gamma polynomials of
the associated Eulerian pencil.  It records only the algebraic recurrence and
its two affine components.  The finite-symbol and real-rootedness arguments
belong in later modules.

For a rank `n`, the operator is
`f ↦ (1 + 2 n X) f + X (1 - 4 X) f'`.  The rank-two seed is
`1 + a X`, whose constant and parameter components are `gammaU 2 = 1` and
`gammaV 2 = X`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The gamma-pencil step at rank `n`:
`f ↦ (1 + 2 n X) f + X (1 - 4 X) f'`. -/
def gammaOperator (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  oreAffineDerivativeLinearMap
    (1 + C (2 * n : ℝ) * X) (X * (1 - C (4 : ℝ) * X))

@[simp]
theorem gammaOperator_apply (n : ℕ) (p : ℝ[X]) :
    gammaOperator n p =
      (1 + C (2 * n : ℝ) * X) * p + X * (1 - C (4 : ℝ) * X) * p.derivative :=
  rfl

@[simp]
theorem gammaOperator_zero (n : ℕ) : gammaOperator n (0 : ℝ[X]) = 0 :=
  (gammaOperator n).map_zero

@[simp]
theorem gammaOperator_add (n : ℕ) (p q : ℝ[X]) :
    gammaOperator n (p + q) = gammaOperator n p + gammaOperator n q :=
  (gammaOperator n).map_add p q

@[simp]
theorem gammaOperator_smul (n : ℕ) (a : ℝ) (p : ℝ[X]) :
    gammaOperator n (a • p) = a • gammaOperator n p :=
  (gammaOperator n).map_smul a p

/-- The gamma operator leaves the constant coefficient unchanged. -/
@[simp]
theorem gammaOperator_constantCoeff (n : ℕ) (p : ℝ[X]) :
    (gammaOperator n p).constantCoeff = p.constantCoeff := by
  simp [gammaOperator]

/-- The constant component of the gamma pencil, indexed by its Eulerian rank.
The values below rank two are set to zero so that the family is total on
natural numbers. -/
def gammaU : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => gammaOperator (n + 2) (gammaU (n + 2))

/-- The parameter component of the gamma pencil, indexed by its Eulerian rank.
The values below rank two are set to zero so that the family is total on
natural numbers. -/
def gammaV : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | 2 => X
  | n + 3 => gammaOperator (n + 2) (gammaV (n + 2))

@[simp]
theorem gammaU_zero : gammaU 0 = 0 := rfl

@[simp]
theorem gammaU_one : gammaU 1 = 0 := rfl

@[simp]
theorem gammaU_two : gammaU 2 = 1 := rfl

@[simp]
theorem gammaV_zero : gammaV 0 = 0 := rfl

@[simp]
theorem gammaV_one : gammaV 1 = 0 := rfl

@[simp]
theorem gammaV_two : gammaV 2 = X := rfl

/-- The successor equation for the constant gamma component. -/
theorem gammaU_succ_succ_succ (n : ℕ) :
    gammaU (n + 3) = gammaOperator (n + 2) (gammaU (n + 2)) :=
  rfl

/-- The successor equation for the parameter gamma component. -/
theorem gammaV_succ_succ_succ (n : ℕ) :
    gammaV (n + 3) = gammaOperator (n + 2) (gammaV (n + 2)) :=
  rfl

/-- Every constant component from rank two onwards has constant coefficient one.
The index `n + 2` presents the natural rank range without a side condition. -/
@[simp]
theorem gammaU_constantCoeff_add_two (n : ℕ) :
    (gammaU (n + 2)).constantCoeff = 1 := by
  induction n with
  | zero => simp [gammaU]
  | succ n ih =>
      change (gammaOperator (n + 2) (gammaU (n + 2))).constantCoeff = 1
      simpa only [gammaOperator_constantCoeff] using ih

/-- Every parameter component from rank two onwards has vanishing constant
coefficient.  The index `n + 2` presents the natural rank range without a
side condition. -/
@[simp]
theorem gammaV_constantCoeff_add_two (n : ℕ) :
    (gammaV (n + 2)).constantCoeff = 0 := by
  induction n with
  | zero => simp [gammaV]
  | succ n ih =>
      change (gammaOperator (n + 2) (gammaV (n + 2))).constantCoeff = 0
      simpa only [gammaOperator_constantCoeff] using ih

/-- The rank-`n` gamma polynomial in the affine parameter `a`. -/
def gammaPencil (a : ℝ) (n : ℕ) : ℝ[X] := gammaU n + a • gammaV n

@[simp]
theorem gammaPencil_two (a : ℝ) : gammaPencil a 2 = 1 + a • X := by
  simp [gammaPencil]

@[simp]
theorem gammaPencil_constantCoeff_add_two (a : ℝ) (n : ℕ) :
    (gammaPencil a (n + 2)).constantCoeff = 1 := by
  change (gammaU (n + 2)).coeff 0 + a * (gammaV (n + 2)).coeff 0 = 1
  rw [show (gammaU (n + 2)).coeff 0 = 1 from
      gammaU_constantCoeff_add_two n,
    show (gammaV (n + 2)).coeff 0 = 0 from
      gammaV_constantCoeff_add_two n]
  simp

/-- The gamma-pencil recurrence.  In particular, the same rank-dependent
operator transports both affine components simultaneously. -/
theorem gammaPencil_succ_succ_succ (a : ℝ) (n : ℕ) :
    gammaPencil a (n + 3) =
      gammaOperator (n + 2) (gammaPencil a (n + 2)) := by
  simp only [gammaPencil, gammaU_succ_succ_succ, gammaV_succ_succ_succ,
    gammaOperator_add, gammaOperator_smul]

end RealRooted
