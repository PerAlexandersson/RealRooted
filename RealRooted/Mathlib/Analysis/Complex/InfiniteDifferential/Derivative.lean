/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Entire differential sums and spatial differentiation

For entire inputs of order below two, the normally convergent differential
series defines an entire function and commutes with every spatial derivative.
-/

public section

open Filter Topology

namespace Complex

/-- Each finite differential partial sum is entire. -/
theorem differentiable_partial_infiniteDifferentialApply {φ f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (N : ℕ) : Differentiable ℂ
    (fun z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)) := by
  apply Differentiable.fun_sum
  intro n _
  exact (((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv _
    (WithTop.coe_lt_top _)).const_mul _).div_const _

/-- The infinite differential image of entire inputs of order below two is entire. -/
theorem differentiable_infiniteDifferentialApply {φ f : ℂ → ℂ} {ρ σ : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2) :
    Differentiable ℂ (infiniteDifferentialApply φ f) := by
  apply differentiableOn_univ.mp
  apply (tendstoLocallyUniformlyOn_univ.mpr
    (tendstoLocallyUniformly_infiniteDifferentialApply hφ hoφ hρ hf hof hσ)).differentiableOn
      (Eventually.of_forall fun N =>
        (differentiable_partial_infiniteDifferentialApply hf N).differentiableOn) isOpen_univ

/-- Spatial derivatives commute with finite differential partial sums. -/
theorem iteratedDeriv_partial_infiniteDifferentialApply {φ f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (N k : ℕ) :
    iteratedDeriv k (fun z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)) =
    fun z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n (iteratedDeriv k f) z / (n.factorial : ℂ) := by
  ext z
  rw [iteratedDeriv_fun_sum (fun n _ =>
    ((((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv _
      (WithTop.coe_lt_top _)).const_mul _).div_const _).contDiff.contDiffAt)]
  apply Finset.sum_congr rfl
  intro n _
  simp only [iteratedDeriv_div_const, iteratedDeriv_const_mul_field,
    iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm k]

/-- Every spatial derivative commutes with a convergent infinite differential operator. -/
theorem iteratedDeriv_infiniteDifferentialApply {φ f : ℂ → ℂ} {ρ σ : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2) (k : ℕ) :
    iteratedDeriv k (infiniteDifferentialApply φ f) =
      infiniteDifferentialApply φ (iteratedDeriv k f) := by
  have hleft :=
    (tendstoLocallyUniformly_infiniteDifferentialApply hφ hoφ hρ hf hof hσ).iteratedDeriv
      (differentiable_partial_infiniteDifferentialApply hf) k
  simp only [iteratedDeriv_partial_infiniteDifferentialApply hf] at hleft
  have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k (WithTop.coe_lt_top _)
  have hright := tendstoLocallyUniformly_infiniteDifferentialApply hφ hoφ hρ hdf
    (hof.iteratedDeriv hf k) hσ
  ext z
  exact tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_univ.mpr hleft).tendsto_at (Set.mem_univ z))
    ((tendstoLocallyUniformlyOn_univ.mpr hright).tendsto_at (Set.mem_univ z))

end Complex
