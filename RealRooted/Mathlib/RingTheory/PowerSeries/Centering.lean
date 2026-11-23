/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient
import RealRooted.Mathlib.RingTheory.PowerSeries.LowDegree
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

import Mathlib.Tactic.TypeStar

/-!
# Centering a formal symbol at its first coefficient

Multiplication by the inverse linear exponential removes the linear term.
The new quadratic coefficient is half the second cumulant.
-/

public section

namespace PowerSeries

variable {R : Type*} [Field R] [Algebra ℚ R]

/-- A constant-one formal symbol has a centered quadratic factorization, with
its constant factor coefficient computed exactly. -/
theorem exists_centered_quadratic_factor {φ : PowerSeries R}
    (h0 : constantCoeff φ = 1) :
    ∃ ψ : PowerSeries R,
      rescale (-coeff 1 φ) (exp R) * φ = 1 + X ^ 2 * ψ ∧
      constantCoeff ψ = coeff 2 φ - coeff 1 φ ^ 2 / 2 := by
  let : CharZero R := algebraRat.charZero R
  let χ := rescale (-coeff 1 φ) (exp R) * φ
  have hφ0 : coeff 0 φ = 1 := by simpa only [coeff_zero_eq_constantCoeff] using h0
  have hχ0 : constantCoeff χ = 1 := by
    change constantCoeff (rescale (-coeff 1 φ) (exp R) * φ) = 1
    rw [map_mul, h0, mul_one, ← coeff_zero_eq_constantCoeff]
    simp
  have hχ1 : coeff 1 χ = 0 := by
    change coeff 1 (rescale (-coeff 1 φ) (exp R) * φ) = 0
    rw [coeff_one_mul]
    norm_num [coeff_rescale_exp, hφ0, ← coeff_zero_eq_constantCoeff]
  have hχ2 : coeff 2 χ = coeff 2 φ - coeff 1 φ ^ 2 / 2 := by
    change coeff 2 (rescale (-coeff 1 φ) (exp R) * φ) = _
    rw [coeff_two_mul]
    norm_num [coeff_rescale_exp, hφ0, ← coeff_zero_eq_constantCoeff]
    ring
  have hdiv : X ^ 2 ∣ χ - 1 := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    have hk' : k = 0 ∨ k = 1 := by lia
    rcases hk' with rfl | rfl
    · simp [coeff_zero_eq_constantCoeff, hχ0]
    · simp [hχ1]
  obtain ⟨ψ, hψ⟩ := hdiv
  have heq : χ = 1 + X ^ 2 * ψ := by
    rw [← hψ]
    ring
  refine ⟨ψ, heq, ?_⟩
  have hcoeff := congrArg (coeff 2) heq
  simpa [coeff_X_pow_mul', coeff_zero_eq_constantCoeff, hχ2] using hcoeff.symm

end PowerSeries
