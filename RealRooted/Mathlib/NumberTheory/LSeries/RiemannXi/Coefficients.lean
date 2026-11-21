/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.CompPow

/-!
# Normalized Taylor coefficients of the Riemann xi function

The real sequence `γ(n) = n! ξ⁽²ⁿ⁾(1/2) / (2n)!` is the exponential Taylor data of
`riemannXiTheta`. This is the normalization used for the xi Jensen polynomials.
-/

@[expose] public section

open Complex

/-- The normalized xi coefficients: the exponential Taylor data of `Θ`. -/
noncomputable def riemannXiCoeff (n : ℕ) : ℝ := (iteratedDeriv n riemannXiTheta 0).re

/-- The derivatives defining the normalized xi coefficients are real. -/
theorem ofReal_riemannXiCoeff (n : ℕ) :
    (riemannXiCoeff n : ℂ) = iteratedDeriv n riemannXiTheta 0 :=
  ofReal_re_iteratedDeriv_zero riemannXiTheta_conj n

/-- The square-variable Taylor data agree with the even-derivative normalization of xi. -/
theorem riemannXiCoeff_eq (n : ℕ) :
    riemannXiCoeff n = (n.factorial : ℝ) / (2 * n).factorial *
      (iteratedDeriv (2 * n) riemannXi (1 / 2)).re := by
  have h := iteratedDeriv_comp_pow_zero (differentiable_riemannXiTheta.analyticAt 0)
    (by norm_num : 0 < 2) n
  have heq : (fun z : ℂ => riemannXiTheta (z ^ 2)) = fun z => riemannXi (1 / 2 + z) :=
    funext riemannXiTheta_sq
  rw [heq, iteratedDeriv_comp_const_add] at h
  simp only [add_zero] at h
  have hc : (riemannXiCoeff n : ℂ) = (n.factorial : ℂ) / (2 * n).factorial *
      iteratedDeriv (2 * n) riemannXi (1 / 2) := by
    rw [h, ofReal_riemannXiCoeff]
    field_simp [Nat.factorial_ne_zero]
  have hr := congrArg Complex.re hc
  simpa using hr

/-- The constant normalized coefficient is nonzero. -/
theorem riemannXiCoeff_zero_ne_zero : riemannXiCoeff 0 ≠ 0 := by
  intro h
  have hc := ofReal_riemannXiCoeff 0
  simp only [h, ofReal_zero, iteratedDeriv_zero] at hc
  exact riemannXiTheta_zero_ne_zero hc.symm
