/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.Chebyshev.Unsmoothing
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ErrorDifference

/-!
# Chebyshev error bounds from Mathlib's Riemann hypothesis

Mathlib's RH implies `psi(x) - x = O(sqrt(x) log(x)^2)` and the corresponding
bound for `theta`. The proof uses the integrated explicit formula, absolute
zero-series convergence, quantitative finite-difference estimates, and the
unconditional removal of higher prime powers.
-/

public section

open Filter Asymptotics

namespace RiemannHypothesis

/-- Mathlib's RH gives a shared positive error constant for both Chebyshev functions. -/
theorem exists_abs_psi_theta_sub_le_sqrt_mul_log_sq (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 25 ≤ x →
      |Chebyshev.psi x - x| ≤ K * (Real.sqrt x * Real.log x ^ 2) ∧
      |Chebyshev.theta x - x| ≤ K * (Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨C, hC, hback, hforward⟩ := hRH.exists_psiIntegralError_sqrt_bounds
  exact Chebyshev.exists_abs_psi_theta_sub_le_of_psiIntegralError_bounds hC.le hback hforward

/-- Under Mathlib's RH, `psi(x) - x` has the classical square-root logarithmic-square error. -/
theorem isBigO_psi_sub_id (hRH : RiemannHypothesis) :
    (fun x : ℝ ↦ Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨K, _, hbound⟩ := hRH.exists_abs_psi_theta_sub_le_sqrt_mul_log_sq
  apply IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (25 : ℝ)] with x hx
  have hw : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hw] using (hbound x hx).1

/-- Under Mathlib's RH, `theta(x) - x` has the classical square-root logarithmic-square error. -/
theorem isBigO_theta_sub_id (hRH : RiemannHypothesis) :
    (fun x : ℝ ↦ Chebyshev.theta x - x) =O[atTop]
      (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2) :=
  Chebyshev.isBigO_theta_sub_id_of_isBigO_psi_sub_id hRH.isBigO_psi_sub_id

end RiemannHypothesis
