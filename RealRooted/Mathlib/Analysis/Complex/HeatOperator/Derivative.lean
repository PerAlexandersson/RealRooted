/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphic heat sums and spatial derivatives

For an entire input of order below two, the heat sum is entire separately in
time and space. Every spatial derivative commutes with the heat operator.
-/

public section

open Filter Topology

namespace Complex

/-- At fixed complex time, the heat series converges locally uniformly in space. -/
theorem tendstoLocallyUniformly_heatOperator_space {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (t : ℂ) :
    TendstoLocallyUniformly
      (fun N z => ∑ n ∈ Finset.range N,
        (-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z)
      (heatOperator t f) atTop := by
  simpa only [Function.comp_def] using
    (tendstoLocallyUniformly_heatOperator hf horder hρ).comp (fun z => (t, z)) (by fun_prop)

/-- At fixed spatial point, the heat series converges locally uniformly in time. -/
theorem tendstoLocallyUniformly_heatOperator_time {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (z : ℂ) :
    TendstoLocallyUniformly
      (fun N t => ∑ n ∈ Finset.range N,
        (-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z)
      (fun t => heatOperator t f z) atTop := by
  simpa only [Function.comp_def] using
    (tendstoLocallyUniformly_heatOperator hf horder hρ).comp (fun t => (t, z)) (by fun_prop)

/-- Every finite heat sum is entire in space. -/
private theorem differentiable_partial_heat {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (t : ℂ) (N : ℕ) : Differentiable ℂ
      (fun z => ∑ n ∈ Finset.range N,
        (-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z) := by
  apply Differentiable.fun_sum
  intro n _
  exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv _
    (WithTop.coe_lt_top _)).const_mul _

/-- Every complex-time heat image is entire in space. -/
theorem differentiable_heatOperator {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (t : ℂ) :
    Differentiable ℂ (heatOperator t f) := by
  apply differentiableOn_univ.mp
  apply (tendstoLocallyUniformlyOn_univ.mpr
    (tendstoLocallyUniformly_heatOperator_space hf horder hρ t)).differentiableOn
      (Eventually.of_forall fun N => (differentiable_partial_heat hf t N).differentiableOn)
      isOpen_univ

/-- At every spatial point, the heat image is entire in complex time. -/
theorem differentiable_heatOperator_time {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (z : ℂ) :
    Differentiable ℂ (fun t => heatOperator t f z) := by
  apply differentiableOn_univ.mp
  apply (tendstoLocallyUniformlyOn_univ.mpr
    (tendstoLocallyUniformly_heatOperator_time hf horder hρ z)).differentiableOn
      (Eventually.of_forall fun N => ?_) isOpen_univ
  apply Differentiable.differentiableOn
  apply Differentiable.fun_sum
  intro n _
  exact ((differentiable_id.neg.pow n).div_const _).mul_const _

/-- Spatial derivatives commute with finite heat sums. -/
private theorem iteratedDeriv_partial_heat {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (t : ℂ) (N k : ℕ) :
    iteratedDeriv k (fun z => ∑ n ∈ Finset.range N,
      (-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z) =
    fun z => ∑ n ∈ Finset.range N,
      (-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) (iteratedDeriv k f) z := by
  ext z
  rw [iteratedDeriv_fun_sum (fun n _ =>
    (((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv _
      (WithTop.coe_lt_top _)).const_mul _).contDiff.contDiffAt)]
  apply Finset.sum_congr rfl
  intro n _
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm k]

/-- Every spatial derivative commutes with the entire heat operator. -/
theorem iteratedDeriv_heatOperator {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (t : ℂ) (k : ℕ) :
    iteratedDeriv k (heatOperator t f) = heatOperator t (iteratedDeriv k f) := by
  have hleft := (tendstoLocallyUniformly_heatOperator_space hf horder hρ t).iteratedDeriv
    (differentiable_partial_heat hf t) k
  simp only [iteratedDeriv_partial_heat hf] at hleft
  have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k (WithTop.coe_lt_top _)
  have hright := tendstoLocallyUniformly_heatOperator_space hdf
    (horder.iteratedDeriv hf k) hρ t
  ext z
  exact tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_univ.mpr hleft).tendsto_at (Set.mem_univ z))
    ((tendstoLocallyUniformlyOn_univ.mpr hright).tendsto_at (Set.mem_univ z))

end Complex
