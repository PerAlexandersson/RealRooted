/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Locally uniform convergence of linear products

Summable real slopes define locally uniformly convergent products of linear
factors on the complex plane.
-/

public section

open Filter Topology

namespace Complex

/-- Uniform convergence on every closed ball centred at `0` gives local uniform convergence. -/
theorem tendstoLocallyUniformly_of_closedBall {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : ∀ R : ℝ, TendstoUniformlyOn F f atTop (Metric.closedBall 0 R)) :
    TendstoLocallyUniformly F f atTop := by
  intro u hu x
  refine ⟨Metric.closedBall 0 (‖x‖ + 1), ?_, h (‖x‖ + 1) u hu⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simp

/-- The partial products of `∏ₖ (1 + yₖ z)` converge locally uniformly when `∑ |yₖ| < ∞`. -/
theorem tendstoLocallyUniformly_prod_one_add (y : ℕ → ℝ) (hy : Summable y) :
    TendstoLocallyUniformly (fun n (z : ℂ) => ∏ k ∈ Finset.range n, (1 + (y k : ℂ) * z))
      (fun z => ∏' k, (1 + (y k : ℂ) * z)) atTop := by
  refine tendstoLocallyUniformly_of_closedBall fun R => ?_
  refine (Summable.hasProdUniformlyOn_nat_one_add (f := fun k (z : ℂ) => (y k : ℂ) * z)
    (isCompact_closedBall 0 R) (hy.norm.mul_right R) ?_
    (fun n => by fun_prop)).tendstoUniformlyOn_finsetRange
  refine Eventually.of_forall fun n z hz => ?_
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (by simpa using hz) (norm_nonneg _)

end Complex
