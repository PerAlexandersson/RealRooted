/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.SmallTypeBound

/-!
# Vanishing exponential type gives convergence to the identity operator

The symbol family may be indexed by any filter. A strictly positive upper
bound for the type is harmless for zero-type symbols and finite product tails.
-/

public section

open Filter Topology

namespace Complex

/-- Normalized entire symbols with exponential-type bounds tending to zero act
locally uniformly like the identity on every entire target of finite order. -/
theorem tendstoLocallyUniformly_infiniteDifferentialApply_of_type_tendsto_zero
    {ι : Type*} {l : Filter ι} {φ : ι → ℂ → ℂ} {B : ι → ℝ}
    (hφ : ∀ i, Differentiable ℂ (φ i)) (hφ0 : ∀ i, φ i 0 = 1)
    (hB : ∀ i, 0 < B i) (hlim : Tendsto B l (𝓝 0))
    (hbound : ∀ i z, ‖φ i z‖ ≤ Real.exp (B i * ‖z‖))
    {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f ρ) :
    TendstoLocallyUniformly (fun i => infiniteDifferentialApply (φ i) f) f l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro S hS
  obtain ⟨R, _, hR⟩ := hS.isBounded.exists_pos_norm_le
  obtain ⟨K, hK, hk⟩ := exists_infiniteDifferentialApply_sub_bound (R := R) hf hof
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hεK : 0 < ε / K := div_pos hε hK
  filter_upwards [hlim.eventually (eventually_lt_nhds hεK),
    hlim.eventually (eventually_lt_nhds zero_lt_one)] with i hi hi1 z hz
  rw [dist_eq_norm, norm_sub_rev]
  apply ((hk (φ i) (hφ i) (hφ0 i) (B i) (hB i) hi1.le (hbound i) z (hR z hz)).2).trans_lt
  exact (mul_lt_mul_of_pos_left hi hK).trans_eq (mul_div_cancel₀ _ hK.ne')

end Complex
