/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindow
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.CumulativeMoments
import RealRooted.Mathlib.NumberTheory.Chebyshev.ShortIntervals
import RealRooted.Mathlib.Analysis.Asymptotics.IncrementBounds
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Prime-window moments under RH

Uniform Chebyshev discrepancy controls every monomial moment of the finite
logarithmically weighted prime window. Under Mathlib's RH, windows of length
`sqrt X * log X ^ 3` have moments converging to `1 / (k + 1)`, the moments of
Lebesgue measure on `[0, 1]`.

The moment error is uniform in `k`. Applications to roots of orthogonal
polynomials still require fixed degree and separate perturbation estimates.
-/

public section

open Filter Set
open scoped Topology

namespace Chebyshev

/-- Chebyshev discrepancy bounds every prime-window monomial moment. -/
theorem abs_primeWindowMoment_sub_le {X H δ : ℝ} (hH : 0 < H)
    (hδ : ∀ u ∈ Icc (0 : ℝ) 1,
      |(theta (X + H * u) - theta X) / H - u| ≤ δ) (k : ℕ) :
    |primeWindowMoment X H k - 1 / ((k : ℝ) + 1)| ≤ 2 * δ := by
  apply Finset.abs_sum_mul_pow_sub_le_of_cumulative_bound
    (primeWindow X H) (fun p ↦ ((p : ℝ) - X) / H) (fun p ↦ Real.log p / H)
  · intro p hp
    exact ⟨(primeWindow_node_mem_Ioc hH hp).1.le, (primeWindow_node_mem_Ioc hH hp).2⟩
  · intro u hu
    rw [sum_primeWindow_weight_node_le hH hu]
    exact hδ u hu

end Chebyshev

namespace RiemannHypothesis

/-- RH gives one eventual `O(1 / log X)` bound for all prime-window moments. -/
theorem eventually_primeWindowMoment_sub_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ k : ℕ,
      |Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3) k -
          1 / ((k : ℝ) + 1)| ≤ C / Real.log X := by
  obtain ⟨C, hC, hbound⟩ := hRH.eventually_theta_increment_div_sqrt_log_cube_le
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hbound, Real.eventually_sqrt_mul_log_cube_pos_le] with X hX hH k
  calc
    _ ≤ 2 * (C / Real.log X) := Chebyshev.abs_primeWindowMoment_sub_le hH.1 hX k
    _ = (2 * C) / Real.log X := by ring

/-- Under RH, every fixed logarithmically weighted prime-window moment tends
to the corresponding uniform moment on `[0, 1]`. -/
theorem tendsto_primeWindowMoment (hRH : RiemannHypothesis) (k : ℕ) :
    Tendsto (fun X : ℝ ↦
      Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3) k)
      atTop (𝓝 (1 / ((k : ℝ) + 1))) := by
  obtain ⟨C, _, hbound⟩ := hRH.eventually_primeWindowMoment_sub_le
  have hlim : Tendsto (fun X : ℝ ↦ C / Real.log X) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hbound, hlim.eventually (gt_mem_nhds hε)] with X hX hsmall
  rw [Real.dist_eq]
  exact (hX k).trans_lt hsmall

end RiemannHypothesis
