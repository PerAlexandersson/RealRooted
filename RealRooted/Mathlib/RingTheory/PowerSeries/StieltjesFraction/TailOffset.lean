/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Coefficients

/-!
# Offset Stieltjes tails

A first-diagonal correction of a finite Jacobi matrix corresponds to the
product of a new Stieltjes step and the original tail. Its Jacobi recursion
shifts the numerator data by two and changes the correction to the second
Stieltjes numerator.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Shifting the numerator sequence shifts the starting index of its formal tail. -/
theorem stieltjesTail_shift (a : ℕ → R) (t s : ℕ) :
    stieltjesTail (fun k => a (k + t)) s = stieltjesTail a (s + t) := by
  ext n
  apply coeff_stieltjesTail_eq_of_prefix
  intro i _
  congr 1
  lia

/-- Adding a first Jacobi diagonal correction preserves the two-step recursion
of a contracted Stieltjes fraction. No sign or nonvanishing assumption is needed. -/
theorem stieltjesStep_mul_tail_eq_jacobiStep (a : ℕ → R) (c : R) :
    stieltjesStep c (stieltjesTail a 0) * stieltjesTail a 0 =
      jacobiStep (c + a 0) (a 0 * a 1)
        (stieltjesStep (a 1) (stieltjesTail (fun k => a (k + 2)) 0) *
          stieltjesTail (fun k => a (k + 2)) 0) := by
  rw [stieltjesTail_shift]
  simp only [Nat.zero_add]
  have ht : stieltjesStep (a 1) (stieltjesTail a 2) = stieltjesTail a 1 :=
    (stieltjesTail_eq_step a 1).symm
  rw [ht]
  apply eq_jacobiStep_of_mul_eq_one
  have h0 := one_sub_mul_stieltjesStep c (stieltjesTail a 0)
  have h1 := one_sub_mul_stieltjesTail a 0
  have h2 : stieltjesTail a 1 =
      1 + C (a 1) * X * stieltjesTail a 2 * stieltjesTail a 1 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using stieltjesTail_eq_one_add a 1
  simp only [map_add, map_mul]
  linear_combination h0 + stieltjesStep c (stieltjesTail a 0) * h1 +
    C (a 0) * X * stieltjesStep c (stieltjesTail a 0) * stieltjesTail a 0 * h2

end PowerSeries
