/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity

/-!
# Derivatives of the square-variable xi function

Every derivative of `riemannXiTheta` is entire, has order at most one half, and is
nonzero at the origin. These unconditional facts allow the real-zero criterion
for the Laguerre--Pólya class to be applied at any fixed derivative index.
-/

public section

/-- Every iterated derivative of the square-variable xi function is entire. -/
theorem differentiable_iteratedDeriv_riemannXiTheta (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n riemannXiTheta) :=
  (differentiable_riemannXiTheta.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by simp)

/-- Every iterated derivative of the square-variable xi function has order at most one half. -/
theorem orderLE_half_iteratedDeriv_riemannXiTheta (n : ℕ) :
    TauCeti.OrderLE (iteratedDeriv n riemannXiTheta) (1 / 2) :=
  orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n

/-- Every iterated derivative of the square-variable xi function has order at most one. -/
theorem orderLE_iteratedDeriv_riemannXiTheta (n : ℕ) :
    TauCeti.OrderLE (iteratedDeriv n riemannXiTheta) 1 :=
  orderLE_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n

/-- Positivity of the xi Taylor data excludes vanishing at zero for every derivative. -/
theorem iteratedDeriv_riemannXiTheta_zero_ne_zero (n : ℕ) :
    iteratedDeriv n riemannXiTheta 0 ≠ 0 := by
  rw [← ofReal_riemannXiCoeff]
  exact_mod_cast (riemannXiCoeff_pos n).ne'
