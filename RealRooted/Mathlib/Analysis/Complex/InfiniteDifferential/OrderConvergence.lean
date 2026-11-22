/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderBound
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Differential-series convergence under reciprocal growth bounds

Positive upper growth exponents `p` and `q` with `1/p + 1/q > 1` suffice for
absolute and locally uniform convergence of the entire differential series.
Neither exponent is individually required to be below two.
-/

public section

open Filter Topology

namespace Complex

/-- The reciprocal growth condition gives absolute convergence of the
infinite differential series. -/
theorem summable_norm_infiniteDifferentialApply_of_order {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖) := by
  obtain ⟨B, hB, hbound⟩ := exists_summable_infiniteDifferentialApply_bound
    (R := ‖z‖) hφ hoφ hp hρ hf hof hq hσ hsum
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbound n z le_rfl) hB

/-- The reciprocal growth condition gives uniform convergence on every disk. -/
theorem tendstoUniformlyOn_infiniteDifferentialApply_of_order {φ f : ℂ → ℂ} {ρ σ p q R : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))
      (infiniteDifferentialApply φ f) atTop {z | ‖z‖ ≤ R} := by
  obtain ⟨B, hB, hbound⟩ := exists_summable_infiniteDifferentialApply_bound
    hφ hoφ hp hρ hf hof hq hσ hsum
  exact tendstoUniformlyOn_tsum_nat hB hbound

/-- The reciprocal growth condition gives locally uniform convergence in space. -/
theorem tendstoLocallyUniformly_infiniteDifferentialApply_of_order {φ f : ℂ → ℂ}
    {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))
      (infiniteDifferentialApply φ f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, _, hbound⟩ := hK.isBounded.exists_pos_norm_le
  exact (tendstoUniformlyOn_infiniteDifferentialApply_of_order (R := R)
    hφ hoφ hp hρ hf hof hq hσ hsum).mono hbound

end Complex
