/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder

import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Bounds

/-!
# Entire infinite differential operators

If an entire symbol and target each have growth order below two, their
differential series converges absolutely and locally uniformly in space.
The symbol uses exponential Taylor coefficients: its nth derivative at zero
is divided by n factorial before acting on the nth derivative of the target.
-/

@[expose] public section

open Filter Topology

namespace Complex

/-- The infinite differential operator associated with an entire symbol. -/
noncomputable def infiniteDifferentialApply (φ f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)

/-- The differential series is absolutely convergent when both entire inputs
have order strictly below two. -/
theorem summable_norm_infiniteDifferentialApply {φ f : ℂ → ℂ} {ρ σ : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2) (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖) := by
  obtain ⟨M, _, hM⟩ := exists_infinite_differential_term_bound hφ hoφ hρ hf hof hσ (norm_nonneg z)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hM n z le_rfl)
    ((summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left M)

/-- Infinite differential partial sums converge uniformly on every spatial disk. -/
theorem tendstoUniformlyOn_infiniteDifferentialApply {φ f : ℂ → ℂ} {ρ σ : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))
      (infiniteDifferentialApply φ f) atTop {z | ‖z‖ ≤ R} := by
  obtain ⟨M, _, hM⟩ := exists_infinite_differential_term_bound hφ hoφ hρ hf hof hσ hR
  exact tendstoUniformlyOn_tsum_nat
    ((summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left M) hM

/-- Infinite differential partial sums converge locally uniformly in space. -/
theorem tendstoLocallyUniformly_infiniteDifferentialApply {φ f : ℂ → ℂ} {ρ σ : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hρ : ρ < 2)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hσ : σ < 2) :
    TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))
      (infiniteDifferentialApply φ f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  exact (tendstoUniformlyOn_infiniteDifferentialApply hφ hoφ hρ hf hof hσ hR.le).mono hbound

end Complex
