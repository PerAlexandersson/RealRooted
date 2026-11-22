/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindow
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.ContinuousTests
import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowMoments
import RealRooted.Mathlib.Analysis.Asymptotics.IncrementBounds

/-!
# Continuous weights on logarithmic prime windows

Under Mathlib's RH, logarithmically weighted prime windows of length
`sqrt X * log X ^ 3` converge against every continuous test on `[0, 1]`.
Consequently any fixed continuous reference weight gives the corresponding
weighted moment limits. This is qualitative convergence; no discrepancy rate
for arbitrary continuous weights is asserted.
-/

public section

open Filter
open scoped Topology

namespace Chebyshev

/-- The moment of a finite logarithmic prime window with an additional reference weight.
The base logarithmic weights are divided by the window length, with no mass normalization. -/
@[expose] noncomputable def primeWindowWeightedMoment (W : ℝ → ℝ) (X H : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ primeWindow X H, (Real.log p / H) *
    ((((p : ℝ) - X) / H) ^ k * W (((p : ℝ) - X) / H))

end Chebyshev

namespace RiemannHypothesis

/-- Under RH, finite logarithmic prime-window sums converge against every continuous test
on the unit interval. Positivity and the mass bound are obtained from the actual prime weights. -/
theorem tendsto_primeWindow_sum_mul (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun X : ℝ ↦
      ∑ p ∈ Chebyshev.primeWindow X (Real.sqrt X * Real.log X ^ 3),
        (Real.log p / (Real.sqrt X * Real.log X ^ 3)) *
          f (((p : ℝ) - X) / (Real.sqrt X * Real.log X ^ 3)))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  apply Finset.tendsto_sum_mul_of_tendsto_sum_mul_pow
    (fun X : ℝ ↦ Chebyshev.primeWindow X (Real.sqrt X * Real.log X ^ 3))
    (fun X p ↦ ((p : ℝ) - X) / (Real.sqrt X * Real.log X ^ 3))
    (fun X p ↦ Real.log p / (Real.sqrt X * Real.log X ^ 3))
  · filter_upwards [Real.eventually_sqrt_mul_log_cube_pos_le] with X hX p hp
    have hn := Chebyshev.primeWindow_node_mem_Ioc hX.1 hp
    exact ⟨hn.1.le, hn.2⟩
  · filter_upwards [Real.eventually_sqrt_mul_log_cube_pos_le] with X hX p hp
    exact (Chebyshev.primeWindow_weight_pos hX.1 hp).le
  · intro k
    exact hRH.tendsto_primeWindowMoment k
  · exact hf

/-- Every fixed continuous reference weight on `[0, 1]` has the expected prime-window moment
limit under RH. Nonnegativity is not needed for this integral limit itself. -/
theorem tendsto_primeWindowWeightedMoment (hRH : RiemannHypothesis) {W : ℝ → ℝ}
    (hW : ContinuousOn W (Set.Icc (0 : ℝ) 1)) (k : ℕ) :
    Tendsto (fun X : ℝ ↦
      Chebyshev.primeWindowWeightedMoment W X (Real.sqrt X * Real.log X ^ 3) k)
      atTop (𝓝 (∫ t in (0 : ℝ)..1, t ^ k * W t)) := by
  exact hRH.tendsto_primeWindow_sum_mul ((continuousOn_id.pow k).mul hW)

end RiemannHypothesis
