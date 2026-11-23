/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Jacobi.Orthogonality.Integral
public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowContinuous
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Jacobi-weighted prime-window moments under RH

For fixed `α, β ≥ 0`, the shifted Jacobi weight is continuous on the closed
unit interval. Under Mathlib's RH the weighted prime moments therefore tend
to the existing unnormalized shifted Jacobi moments. Zero parameters are
included. A quantitative rate is not inferred from continuity.
-/

public section

open Filter
open scoped Topology Polynomial

namespace RealRooted

/-- Nonnegative Jacobi exponents give a continuous weight, including the cases where an exponent
is zero. No differentiability at either endpoint is asserted. -/
theorem continuous_shiftedJacobiWeight {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Continuous (shiftedJacobiWeight α β) := by
  exact (Real.continuous_rpow_const hα).mul
    ((Real.continuous_rpow_const hβ).comp (continuous_const.sub continuous_id))

end RealRooted

namespace RiemannHypothesis

/-- Under RH, Jacobi-weighted prime-window moments converge to the shifted Jacobi moments for
all fixed nonnegative real parameters. The normalization is the beta weight itself, not a
probability normalization; this is the moment sequence used by the monic Jacobi family. -/
theorem tendsto_primeWindowWeightedMoment_jacobi (hRH : RiemannHypothesis)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (k : ℕ) :
    Tendsto (fun X : ℝ ↦
      Chebyshev.primeWindowWeightedMoment (RealRooted.shiftedJacobiWeight α β)
        X (Real.sqrt X * Real.log X ^ 3) k)
      atTop (𝓝 (RealRooted.shiftedJacobiMoment α β k)) := by
  have hlim := hRH.tendsto_primeWindowWeightedMoment
    (RealRooted.continuous_shiftedJacobiWeight hα hβ).continuousOn k
  have hint : (∫ t in (0 : ℝ)..1, t ^ k * RealRooted.shiftedJacobiWeight α β t) =
      RealRooted.shiftedJacobiMoment α β k := by
    have h := RealRooted.shiftedJacobiFunctional_eq_integral
      (by linarith : -1 < α) (by linarith : -1 < β) (Polynomial.X ^ k)
    simpa only [RealRooted.shiftedJacobiFunctional_X_pow, RealRooted.shiftedJacobiIntegrand,
      Polynomial.eval_pow, Polynomial.eval_X] using h.symm
  rwa [hint] at hlim

end RiemannHypothesis
