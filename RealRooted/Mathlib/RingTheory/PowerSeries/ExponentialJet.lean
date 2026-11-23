/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient
import Mathlib.Tactic.Ring

import Mathlib.Tactic.TypeStar

/-!
# Centering at a matching exponential jet
-/

public section

namespace PowerSeries

variable {R : Type*} [Field R] [Algebra ℚ R]

/-- If a formal series agrees with a linear exponential below order `p`,
centering factors out `X^p`. The first centered coefficient is the exact
ordinary-coefficient discrepancy at order `p`. -/
theorem exists_centered_factor_of_exponential_jet {φ : PowerSeries R}
    (a : R) (p : ℕ)
    (hjet : ∀ k < p, coeff k φ = a ^ k / (k.factorial : R)) :
    ∃ ψ : PowerSeries R,
      rescale (-a) (exp R) * φ = 1 + X ^ p * ψ ∧
      constantCoeff ψ = coeff p φ - a ^ p / (p.factorial : R) := by
  have hdiv : X ^ p ∣ φ - rescale a (exp R) := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    rw [map_sub, hjet k hk, coeff_rescale_exp, sub_self]
  obtain ⟨q, hq⟩ := hdiv
  have hφ : φ = rescale a (exp R) + X ^ p * q := by
    rw [← hq]
    ring
  have hcancel : rescale (-a) (exp R) * rescale a (exp R) = 1 := by
    rw [exp_mul_exp_eq_exp_add, neg_add_cancel]
    simp
  refine ⟨rescale (-a) (exp R) * q, ?_, ?_⟩
  · rw [hφ, mul_add, hcancel]
    congr 1
    ring
  · have hcoeff := congrArg (coeff p) hq
    have hq0 : constantCoeff q = coeff p φ - a ^ p / (p.factorial : R) := by
      simpa [coeff_X_pow_mul', coeff_rescale_exp, coeff_zero_eq_constantCoeff, div_eq_mul_inv]
        using hcoeff.symm
    rw [map_mul, hq0, ← coeff_zero_eq_constantCoeff]
    simp

end PowerSeries
