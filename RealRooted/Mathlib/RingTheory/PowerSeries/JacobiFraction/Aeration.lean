/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform
import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Translation

import Mathlib.Tactic.TypeStar

/-!
# Aerating a formal Stieltjes fraction

Substitution of `X^2` inserts zero odd coefficients. It turns a Stieltjes
tail into a Jacobi tail with zero diagonal and the same numerator sequence.
Binomial translation then makes every diagonal equal to the shift.

See Sokal, arXiv:1903.12455v2, equations (9)-(10).
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Substitution of the square variable inserts zero between successive coefficients. -/
theorem coeff_subst_X_sq (f : R⟦X⟧) (n : ℕ) :
    coeff n (f.subst (X ^ 2 : R⟦X⟧)) =
      if n % 2 = 0 then coeff (n / 2) f else 0 := by
  rw [coeff_subst_X_pow (by decide)]
  simp only [Nat.dvd_iff_mod_eq_zero, Algebra.algebraMap_self, RingHom.id_apply]

/-- An aerated Stieltjes step is a Jacobi step with zero diagonal. -/
theorem subst_X_sq_stieltjesStep (a : R) (f : R⟦X⟧) :
    (stieltjesStep a f).subst (X ^ 2 : R⟦X⟧) =
      jacobiStep 0 a (f.subst (X ^ 2 : R⟦X⟧)) := by
  have hy : HasSubst (X ^ 2 : R⟦X⟧) := .of_constantCoeff_zero' (by simp)
  have h := congrArg (substAlgHom (R := R) hy) (one_sub_mul_stieltjesStep a f)
  simp only [map_mul, map_sub, map_one, coe_substAlgHom, subst_C, ← C_apply,
    subst_X hy] at h
  apply eq_jacobiStep_of_mul_eq_one
  simpa only [map_zero, zero_mul, sub_zero] using h

/-- Every aerated Stieltjes tail satisfies the zero-diagonal Jacobi recurrence. -/
theorem subst_X_sq_stieltjesTail_eq_step (a : ℕ → R) (n : ℕ) :
    (stieltjesTail a n).subst (X ^ 2 : R⟦X⟧) =
      jacobiStep 0 (a n) ((stieltjesTail a (n + 1)).subst (X ^ 2 : R⟦X⟧)) := by
  rw [stieltjesTail_eq_step, subst_X_sq_stieltjesStep]

/-- Translated aerated Stieltjes tails have a constant Jacobi diagonal. -/
theorem binomialTransform_subst_X_sq_stieltjesTail_eq_step
    (c : R) (a : ℕ → R) (n : ℕ) :
    binomialTransform c ((stieltjesTail a n).subst (X ^ 2 : R⟦X⟧)) =
      jacobiStep c (a n)
        (binomialTransform c ((stieltjesTail a (n + 1)).subst (X ^ 2 : R⟦X⟧))) := by
  rw [subst_X_sq_stieltjesTail_eq_step, binomialTransform_jacobiStep, zero_add]

end PowerSeries
