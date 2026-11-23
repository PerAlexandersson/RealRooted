/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Positive Gaussian bounds within the strict product threshold
-/

public section

namespace Real

/-- The strict product condition survives a small simultaneous increase,
including when one or both original coefficients vanish. -/
theorem exists_pos_gaussian_coefficients {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : 4 * α * β < 1) :
    ∃ a b : ℝ, α < a ∧ β < b ∧ 0 < a ∧ 0 < b ∧ 4 * a * b < 1 := by
  have hopen : IsOpen {t : ℝ | 4 * (α + t) * (β + t) < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hzero : (0 : ℝ) ∈ {t : ℝ | 4 * (α + t) * (β + t) < 1} := by
    simpa only [Set.mem_ofPred_eq, add_zero] using hab
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  have hh : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  exact ⟨α + r / 2, β + r / 2, by linarith, by linarith,
    by linarith, by linarith, hball hh⟩

end Real
