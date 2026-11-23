/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

/-!
# Formal matrix resolvents

The generating series of the entries of `A^n` form the inverse of `I - X A`.
The construction and identity are purely formal and require no bound on the
matrix or numerical convergence of a geometric series.
-/

public section

open PowerSeries
open scoped BigOperators

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The matrix of generating series of entries of natural powers of `A`. -/
@[expose] noncomputable def powerSeriesResolvent (A : Matrix ι ι R) : Matrix ι ι R⟦X⟧ :=
  fun i j => PowerSeries.mk fun n => (A ^ n) i j

/-- Formal resolvent coefficients are entries of matrix powers. -/
@[simp] theorem coeff_powerSeriesResolvent (A : Matrix ι ι R) (n : ℕ) (i j : ι) :
    PowerSeries.coeff n (powerSeriesResolvent A i j) = (A ^ n) i j := by
  simp only [powerSeriesResolvent, PowerSeries.coeff_mk]

/-- The constant coefficient matrix of a formal resolvent is the identity. -/
@[simp] theorem constantCoeff_powerSeriesResolvent (A : Matrix ι ι R) (i j : ι) :
    PowerSeries.constantCoeff (powerSeriesResolvent A i j) = (1 : Matrix ι ι R) i j := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_powerSeriesResolvent, pow_zero]

/-- The row recurrence for formal matrix resolvents. -/
theorem powerSeriesResolvent_eq_one_add (A : Matrix ι ι R) (i j : ι) :
    powerSeriesResolvent A i j = C ((1 : Matrix ι ι R) i j) +
      X * ∑ l, C (A i l) * powerSeriesResolvent A l j := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
        pow_succ', Matrix.mul_apply]

/-- The formal resolvent is a right inverse of `I - X A`. -/
theorem one_sub_mul_powerSeriesResolvent (A : Matrix ι ι R) :
    (1 - (X : R⟦X⟧) • A.map C) * powerSeriesResolvent A = 1 := by
  apply Matrix.ext
  intro i j
  have h := powerSeriesResolvent_eq_one_add A i j
  calc
    ((1 - (X : R⟦X⟧) • A.map C) * powerSeriesResolvent A) i j =
        powerSeriesResolvent A i j -
          X * ∑ l, C (A i l) * powerSeriesResolvent A l j := by
      rw [sub_mul]
      simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply]
    _ = C ((1 : Matrix ι ι R) i j) := by linear_combination h
    _ = (1 : Matrix ι ι R⟦X⟧) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- The formal resolvent is also a left inverse of `I - X A`. -/
theorem powerSeriesResolvent_mul_one_sub (A : Matrix ι ι R) :
    powerSeriesResolvent A * (1 - (X : R⟦X⟧) • A.map C) = 1 :=
  mul_eq_one_comm.mp (one_sub_mul_powerSeriesResolvent A)

/-- The nonsingular matrix inverse of `I - X A` is its formal resolvent. -/
theorem inv_one_sub_X_smul_map_C (A : Matrix ι ι R) :
    (1 - (X : R⟦X⟧) • A.map C)⁻¹ = powerSeriesResolvent A :=
  Matrix.inv_eq_right_inv (one_sub_mul_powerSeriesResolvent A)

end Matrix
