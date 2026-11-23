/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.MeasureTheory.Measure.ExactMomentSupport
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainCoefficientBound

/-!
# Compact support without initial-parameter normalization
-/

public section

open PowerSeries

namespace MeasureTheory

/-- Bounded chain parameters force the exact compact support even when the
initial parameter is an arbitrary member of `[0,1]`. -/
theorem ae_mem_Icc_of_bounded_chain_moments {mu : Measure ℝ} {L mass : ℝ}
    (hL : 0 ≤ L) (hmass : 0 ≤ mass) {g : ℕ → ℝ}
    (hg : ∀ n, g n ∈ Set.Icc 0 1) (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu)
    (hmom : ∀ n, (∫ x : ℝ, x ^ n ∂mu) =
      mass * coeff n (stieltjesTail (chainStieltjesNumerators L g) 0)) :
    ∀ᵐ x ∂mu, x ∈ Set.Icc 0 L := by
  have hbound (n : ℕ) : (∫ x : ℝ, x ^ (2 * n) ∂mu) ≤ mass * L ^ (2 * n) := by
    rw [hmom]
    exact mul_le_mul_of_nonneg_left (coeff_chainStieltjes_le_pow hL hg (2 * n)) hmass
  have habs := ae_abs_le_of_even_moment_bound hL (fun n => hint (2 * n)) hbound
  filter_upwards [hpos, habs] with x hx hxb
  exact ⟨hx, (le_abs_self x).trans hxb⟩

end MeasureTheory
