/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.MeasureTheory.Measure.ChainMomentSupport
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.CatalanBound
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainAeration
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Moment

/-!
# The sharp coefficient bound for bounded chain parameters

The coefficient bound is `L^n` even when the initial parameter is any value
in `[0,1]`. Replacing only the initial parameter by zero increases the first
numerator; all later numerators stay fixed. Formal coefficient monotonicity
then reduces to the compact-support result with initial parameter zero.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- Normalized chain coefficients satisfy the moment bound from compact support. -/
private theorem coeff_chain_le_pow_of_zero {L : ℝ} (hL : 0 ≤ L)
    {g : ℕ → ℝ} (hg0 : g 0 = 0) (hg : ∀ n, g n ∈ Set.Icc 0 1) (n : ℕ) :
    coeff n (stieltjesTail (chainStieltjesNumerators L g) 0) ≤ L ^ n := by
  obtain ⟨mu, hfin, hpos, hmom⟩ := exists_measure_moments_stieltjesTail
    (chainStieltjesNumerators L g) (chainStieltjesNumerators_nonneg hL hg)
    (show (0 : ℝ) ≤ 1 from zero_le_one)
  let : IsFiniteMeasure mu := hfin
  have hs := ae_mem_Icc_of_chain_moments hL zero_le_one hg0 hg hpos
    (fun k => (hmom k).1) (fun k => (hmom k).2)
  have hmass : mu.real Set.univ = 1 := by simpa using (hmom 0).2
  calc
    coeff n (stieltjesTail (chainStieltjesNumerators L g) 0) =
        ∫ x : ℝ, x ^ n ∂mu := by simpa only [one_mul] using (hmom n).2.symm
    _ ≤ ∫ _x : ℝ, L ^ n ∂mu := by
      apply integral_mono_ae (hmom n).1 (integrable_const _)
      filter_upwards [hs] with x hx
      exact pow_le_pow_left₀ hx.1 hx.2 n
    _ = L ^ n := by simp [hmass, smul_eq_mul]

/-- Every chain with parameters in `[0,1]` satisfies the sharp geometric
coefficient bound, with no initial-parameter normalization. -/
theorem coeff_chainStieltjes_le_pow {L : ℝ} (hL : 0 ≤ L)
    {g : ℕ → ℝ} (hg : ∀ n, g n ∈ Set.Icc 0 1) (n : ℕ) :
    coeff n (stieltjesTail (chainStieltjesNumerators L g) 0) ≤ L ^ n := by
  classical
  let g' : ℕ → ℝ := fun k => if k = 0 then 0 else g k
  have hg0' : g' 0 = 0 := by simp [g']
  have hg' (k : ℕ) : g' k ∈ Set.Icc 0 1 := by
    by_cases hk : k = 0
    · simp [g', hk]
    · simpa only [g', ite_eq_right hk] using hg k
  have hnum (k : ℕ) : chainStieltjesNumerators L g k ≤ chainStieltjesNumerators L g' k := by
    cases k with
    | zero =>
        simp only [chainStieltjesNumerators, g', ite_eq_left rfl,
          show (0 + 1 : ℕ) ≠ 0 by decide, ite_false, sub_zero, mul_one]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (sub_le_self 1 (hg 0).1) hL) (hg 1).1
    | succ k => simp [chainStieltjesNumerators, g']
  exact (coeff_stieltjesTail_mono (chainStieltjesNumerators_nonneg hL hg) hnum n 0).trans
    (coeff_chain_le_pow_of_zero hL hg0' hg' n)

end PowerSeries
