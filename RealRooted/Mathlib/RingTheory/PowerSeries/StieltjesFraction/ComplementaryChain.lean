/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Complementary
import Mathlib.Tactic.TypeStar

/-!
# Complementation of normalized Wall parameters

Complement every positive-index parameter and reset the initial parameter
to zero. Complementing the initial zero as well would give the wrong first
numerator, so the boundary is explicit in the definition.
-/

public section

namespace PowerSeries

/-- The normalized complementary Wall parameters keep the initial parameter
zero and complement every subsequent parameter. -/
@[expose] def complementaryChainParameters {R : Type*} [Zero R] [One R] [Sub R]
    (g : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => 1 - g (n + 1)

/-- The complementary chain has initial parameter zero. -/
@[simp] theorem complementaryChainParameters_zero {R : Type*} [Zero R] [One R] [Sub R]
    (g : ℕ → R) : complementaryChainParameters g 0 = 0 := rfl

/-- Positive-index parameters are complemented. -/
@[simp] theorem complementaryChainParameters_succ {R : Type*} [Zero R] [One R] [Sub R]
    (g : ℕ → R) (n : ℕ) : complementaryChainParameters g (n + 1) = 1 - g (n + 1) := rfl

/-- Complementing preserves the closed unit interval, including its endpoints. -/
theorem complementaryChainParameters_mem_Icc {g : ℕ → ℝ}
    (hg : ∀ n, g n ∈ Set.Icc 0 1) (n : ℕ) :
    complementaryChainParameters g n ∈ Set.Icc 0 1 := by
  cases n with
  | zero => exact ⟨le_rfl, zero_le_one⟩
  | succ n =>
    exact ⟨sub_nonneg.mpr (hg (n + 1)).2, sub_le_self _ (hg (n + 1)).1⟩

/-- Normalized complementary chain fractions have reciprocal-geometric
product. The identity needs no sign restriction on the real parameters or scale. -/
theorem stieltjesTail_chain_mul_complementary (L : ℝ) {g : ℕ → ℝ} (hg0 : g 0 = 0) :
    stieltjesTail (chainStieltjesNumerators L g) 0 *
      stieltjesTail (chainStieltjesNumerators L (complementaryChainParameters g)) 0 =
        stieltjesStep L 1 := by
  apply stieltjesTail_mul_of_complementary_chain (u := fun n => g (n + 1))
  · simp only [chainStieltjesNumerators, hg0, sub_zero, mul_one]
  · simp only [chainStieltjesNumerators, complementaryChainParameters_zero,
      complementaryChainParameters_succ, sub_zero, mul_one]
  · intro n
    rfl
  · intro n
    simp only [chainStieltjesNumerators, complementaryChainParameters_succ, sub_sub_cancel]

end PowerSeries
