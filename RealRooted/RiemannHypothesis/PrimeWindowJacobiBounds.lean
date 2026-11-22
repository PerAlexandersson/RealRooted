/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowContinuous
public import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.RiemannHypothesis.PrimeWindowJacobi
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.CumulativeBeta
import RealRooted.Mathlib.NumberTheory.Chebyshev.ShortIntervals
import RealRooted.Mathlib.Analysis.Asymptotics.IncrementBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative Jacobi-weighted prime-window moments

A finite cumulative error at most `δ` gives Jacobi-weighted moment error at
most `2δ`, for all nonnegative Jacobi parameters and every natural moment
index. Under Mathlib's RH, the actual prime-window error is consequently
`O(1 / log X)`. The weight convention is `t^α (1-t)^β`, matching the native
shifted Jacobi family. Endpoint fractional powers are handled by integrable
interior derivatives, not by a false endpoint `C¹` assumption.
-/

public section

open Filter
open scoped Topology

namespace RealRooted

/-- A finite cumulative discrepancy controls the unnormalized shifted Jacobi moments.
The weights may be signed and nodes may repeat or equal either endpoint. -/
theorem abs_sum_mul_pow_shiftedJacobiWeight_sub_le {ι : Type*}
    (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (k : ℕ) :
    |(∑ i ∈ s, w i * (r i ^ k * shiftedJacobiWeight α β (r i))) -
        shiftedJacobiMoment α β k| ≤ 2 * δ := by
  have hsum : (∑ i ∈ s, w i * (r i ^ k * shiftedJacobiWeight α β (r i))) =
      ∑ i ∈ s, w i * (r i ^ (α + (k : ℝ)) * (1 - r i) ^ β) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.rpow_add_of_nonneg (hr i hi).1 hα (Nat.cast_nonneg k), Real.rpow_natCast]
    dsimp only [shiftedJacobiWeight]
    ring
  rw [hsum, shiftedJacobiMoment_eq_integral (by linarith : -1 < α)
    (by linarith : -1 < β) k]
  exact Finset.abs_sum_beta_weight_sub_le_of_cumulative_bound s r w hr hδ
    (by positivity : 0 ≤ α + (k : ℝ)) hβ

end RealRooted

namespace Chebyshev

/-- Chebyshev discrepancy bounds every native Jacobi-weighted prime-window moment. -/
theorem abs_primeWindowWeightedMoment_jacobi_sub_le {X H δ α β : ℝ}
    (hH : 0 < H) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hδ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |(theta (X + H * u) - theta X) / H - u| ≤ δ) (k : ℕ) :
    |primeWindowWeightedMoment (RealRooted.shiftedJacobiWeight α β) X H k -
        RealRooted.shiftedJacobiMoment α β k| ≤ 2 * δ := by
  apply RealRooted.abs_sum_mul_pow_shiftedJacobiWeight_sub_le
    (primeWindow X H) (fun p ↦ ((p : ℝ) - X) / H) (fun p ↦ Real.log p / H)
  · intro p hp
    have hn := primeWindow_node_mem_Ioc hH hp
    exact ⟨hn.1.le, hn.2⟩
  · intro u hu
    rw [sum_primeWindow_weight_node_le hH hu]
    exact hδ u hu
  · exact hα
  · exact hβ

end Chebyshev

namespace RiemannHypothesis

/-- Under RH, every Jacobi-weighted prime-window moment has eventual error `C / log X`.
The moment-error bound is uniform in the natural moment index; fixed-degree polynomial and
root applications still require their separate nondegeneracy and perturbation arguments. -/
theorem eventually_primeWindowWeightedMoment_jacobi_sub_le (hRH : RiemannHypothesis)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ k : ℕ,
      |Chebyshev.primeWindowWeightedMoment (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) k -
          RealRooted.shiftedJacobiMoment α β k| ≤ C / Real.log X := by
  obtain ⟨C, hC, hbound⟩ := hRH.eventually_theta_increment_div_sqrt_log_cube_le
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hbound, Real.eventually_sqrt_mul_log_cube_pos_le] with X hX hH k
  calc
    _ ≤ 2 * (C / Real.log X) :=
      Chebyshev.abs_primeWindowWeightedMoment_jacobi_sub_le hH.1 hα hβ hX k
    _ = (2 * C) / Real.log X := by ring

end RiemannHypothesis
