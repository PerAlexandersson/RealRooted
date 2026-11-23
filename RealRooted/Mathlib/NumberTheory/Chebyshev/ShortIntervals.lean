/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.UniformSpace.UniformConvergence
import RealRooted.Mathlib.Analysis.Asymptotics.IncrementBounds
import RealRooted.Mathlib.NumberTheory.Chebyshev.RiemannHypothesis

/-!
# Uniform Chebyshev discrepancy in short intervals under RH

For `H = sqrt X * log X ^ 3`, Mathlib's RH implies that
`(theta (X + H * u) - theta X) / H` converges uniformly to `u ∈ [0, 1]`, with
error `O(1 / log X)`. The subtraction of Chebyshev functions corresponds to
primes in `(X, X + H * u]`: the lower endpoint is excluded and the upper
endpoint included.
-/

public section

open Filter Set

namespace RiemannHypothesis

/-- Under RH, Chebyshev increments in square-root logarithmic-cube windows
have uniform discrepancy bounded by a positive constant divided by `log X`. -/
theorem eventually_theta_increment_div_sqrt_log_cube_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ u ∈ Icc (0 : ℝ) 1,
      |(Chebyshev.theta (X + (Real.sqrt X * Real.log X ^ 3) * u) - Chebyshev.theta X) /
          (Real.sqrt X * Real.log X ^ 3) - u| ≤ C / Real.log X := by
  obtain ⟨K, hK, herr⟩ := hRH.exists_abs_psi_theta_sub_le_sqrt_mul_log_sq
  refine ⟨9 * K, by positivity, ?_⟩
  exact Real.eventually_increment_div_sqrt_log_cube_le hK.le
    (fun y hy ↦ (herr y hy).2)

/-- Under RH, normalized Chebyshev increments in square-root logarithmic-cube
windows converge uniformly to Lebesgue interval lengths on `[0, 1]`. -/
theorem tendstoUniformlyOn_theta_increment_div_sqrt_log_cube (hRH : RiemannHypothesis) :
    TendstoUniformlyOn
      (fun X u : ℝ ↦
        (Chebyshev.theta (X + (Real.sqrt X * Real.log X ^ 3) * u) - Chebyshev.theta X) /
          (Real.sqrt X * Real.log X ^ 3))
      (fun u ↦ u) atTop (Icc (0 : ℝ) 1) := by
  obtain ⟨K, hK, herr⟩ := hRH.exists_abs_psi_theta_sub_le_sqrt_mul_log_sq
  exact Real.tendstoUniformlyOn_increment_div_sqrt_log_cube hK.le
    (fun y hy ↦ (herr y hy).2)

end RiemannHypothesis
