/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder

import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Bounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Entire backward heat series

For an entire function of growth order strictly below two, the series defining
`exp (-t D²)` converges absolutely for every complex time and spatial point,
and locally uniformly jointly in both variables.
-/

@[expose] public section

open Filter Topology

namespace Complex

/-- The backward heat operator defined by its even-derivative series. -/
noncomputable def heatOperator (t : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z

/-- The entire heat series converges absolutely at every complex time and point. -/
theorem summable_norm_heatOperator {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f)
    (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (t z : ℂ) :
    Summable (fun n : ℕ => ‖(-t) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f z‖) := by
  obtain ⟨M, _, hM⟩ := exists_heat_term_bound hf horder hρ (norm_nonneg t) (norm_nonneg z)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => hM n (-t) z (by simp) le_rfl)
    ((summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left M)

/-- Partial heat sums converge uniformly whenever complex time and space
are each restricted to a bounded disk. -/
theorem tendstoUniformlyOn_heatOperator {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f)
    (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N (tz : ℂ × ℂ) => ∑ n ∈ Finset.range N,
        (-tz.1) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f tz.2)
      (fun tz => heatOperator tz.1 f tz.2) atTop {tz | ‖tz.1‖ ≤ T ∧ ‖tz.2‖ ≤ R} := by
  obtain ⟨M, _, hM⟩ := exists_heat_term_bound hf horder hρ hT hR
  exact tendstoUniformlyOn_tsum_nat
    ((summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left M)
    (fun n tz htz => hM n (-tz.1) tz.2 (by simpa using htz.1) htz.2)

/-- The heat series converges locally uniformly jointly in complex time and space. -/
theorem tendstoLocallyUniformly_heatOperator {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f)
    (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) :
    TendstoLocallyUniformly
      (fun N (tz : ℂ × ℂ) => ∑ n ∈ Finset.range N,
        (-tz.1) ^ n / (n.factorial : ℂ) * iteratedDeriv (2 * n) f tz.2)
      (fun tz => heatOperator tz.1 f tz.2) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨B, hB, hbound⟩ := hK.isBounded.exists_pos_norm_le
  apply (tendstoUniformlyOn_heatOperator hf horder hρ hB.le hB.le).mono
  intro tz htz
  exact ⟨(norm_fst_le tz).trans (hbound tz htz), (norm_snd_le tz).trans (hbound tz htz)⟩

/-- The heat sum is jointly continuous in complex time and space. -/
theorem continuous_heatOperator {f : ℂ → ℂ} {ρ : ℝ} (hf : Differentiable ℂ f)
    (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) :
    Continuous (fun tz : ℂ × ℂ => heatOperator tz.1 f tz.2) := by
  apply (tendstoLocallyUniformly_heatOperator hf horder hρ).continuous
  apply Filter.Frequently.of_forall
  intro N
  apply continuous_finsetSum
  intro n _
  have hd : Continuous (iteratedDeriv (2 * n) f) :=
    ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv _ (WithTop.coe_lt_top _)).continuous
  exact ((continuous_fst.neg.pow n).div_const _).mul (hd.comp continuous_snd)

/-- At time zero, the heat series recovers its input, with no growth assumption. -/
@[simp] theorem heatOperator_zero (f : ℂ → ℂ) : heatOperator 0 f = f := by
  ext z
  rw [heatOperator, tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

/-- The zero input has zero heat image at every time. -/
@[simp] theorem heatOperator_zero_input (t : ℂ) : heatOperator t (0 : ℂ → ℂ) = 0 := by
  ext z
  simp [heatOperator]

end Complex
