/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Contraction
public import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ActivePrefix

/-!
# Chain parameters from constant Jacobi diagonals

Nonnegative Stieltjes data whose contracted diagonal is constant on the active
prefix give Wall parameters in `[0,1]`. A zero outgoing numerator is represented
by setting the next parameter and all later parameters to zero. No equality
of inactive Jacobi coefficients is required.
-/

public section

namespace PowerSeries

/-- The Stieltjes numerators of a bounded chain-parameter sequence. -/
@[expose] def chainStieltjesNumerators (L : ℝ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  L * (1 - g n) * g (n + 1)

/-- Chain parameters obtained from the odd Stieltjes data on the active prefix. -/
@[expose] noncomputable def stieltjesChainParameters
    (kappa : ℝ) (a b : ℕ → ℝ) : ℕ → ℝ := by
  classical
  exact fun
    | 0 => 0
    | n + 1 => if ∀ k < n + 1, a k ≠ 0 then b (2 * n + 1) / kappa else 0

/-- The chain parameter normalization at the origin. -/
@[simp] theorem stieltjesChainParameters_zero (kappa : ℝ) (a b : ℕ → ℝ) :
    stieltjesChainParameters kappa a b 0 = 0 := rfl

/-- Every extracted chain parameter lies in the closed unit interval. -/
theorem stieltjesChainParameters_mem_Icc {kappa : ℝ} (hk : 0 < kappa)
    {a b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hd : ∀ n, (∀ i < n, a i ≠ 0) → stieltjesJacobiDiagonal b n = kappa)
    (n : ℕ) : stieltjesChainParameters kappa a b n ∈ Set.Icc 0 1 := by
  classical
  cases n with
  | zero => simp
  | succ n =>
      change (if ∀ i < n + 1, a i ≠ 0 then b (2 * n + 1) / kappa else 0) ∈ _
      split_ifs with hact
      · have heq : b (2 * n + 1) + b (2 * n + 2) = kappa := hd (n + 1) hact
        have hbn := hb (2 * n + 2)
        exact ⟨div_nonneg (hb _) hk.le, (div_le_one hk).mpr (by linarith)⟩
      · exact ⟨le_rfl, zero_le_one⟩

/-- The complementary chain parameter recovers the paired even numerator
where the preceding outgoing numerators are nonzero. -/
theorem mul_one_sub_stieltjesChainParameters {kappa : ℝ} (hk : 0 < kappa)
    {a b : ℕ → ℝ}
    (hd : ∀ n, (∀ i < n, a i ≠ 0) → stieltjesJacobiDiagonal b n = kappa)
    (n : ℕ) (hact : ∀ i < n, a i ≠ 0) :
    kappa * (1 - stieltjesChainParameters kappa a b n) = b (2 * n) := by
  classical
  cases n with
  | zero => simpa only [stieltjesChainParameters_zero, sub_zero, mul_one, Nat.mul_zero]
      using (show kappa = b 0 from (hd 0 hact).symm)
  | succ n =>
      have heq : b (2 * n + 1) + b (2 * (n + 1)) = kappa := by
        simpa only [stieltjesJacobiDiagonal, Nat.mul_add, Nat.mul_one] using hd (n + 1) hact
      change kappa * (1 - (if ∀ i < n + 1, a i ≠ 0 then
        b (2 * n + 1) / kappa else 0)) = _
      rw [ite_eq_left hact]
      calc
        _ = kappa - b (2 * n + 1) := by field_simp [ne_of_gt hk]
        _ = _ := by linarith

/-- The extracted chain data agree with every active outgoing Jacobi numerator. -/
theorem chainStieltjesNumerators_eq_on_active {kappa : ℝ} (hk : 0 < kappa)
    {a b : ℕ → ℝ}
    (hd : ∀ n, (∀ i < n, a i ≠ 0) → stieltjesJacobiDiagonal b n = kappa)
    (hn : ∀ n, (∀ i < n, a i ≠ 0) → stieltjesJacobiNumerator b n = a n)
    (n : ℕ) (hact : ∀ i < n, a i ≠ 0) :
    a n = chainStieltjesNumerators (kappa ^ 2) (stieltjesChainParameters kappa a b) n := by
  classical
  by_cases hz : a n = 0
  · have hnext : ¬ ∀ i < n + 1, a i ≠ 0 := fun h => h n (Nat.lt_succ_self n) hz
    simp only [chainStieltjesNumerators, stieltjesChainParameters, ite_eq_right hnext, mul_zero, hz]
  · have hnext : ∀ i < n + 1, a i ≠ 0 := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hact i hlt
      · exact hz
    change a n = kappa ^ 2 * (1 - stieltjesChainParameters kappa a b n) *
      (if ∀ i < n + 1, a i ≠ 0 then b (2 * n + 1) / kappa else 0)
    rw [ite_eq_left hnext]
    have halg : kappa ^ 2 * (1 - stieltjesChainParameters kappa a b n) *
        (b (2 * n + 1) / kappa) =
      (kappa * (1 - stieltjesChainParameters kappa a b n)) * b (2 * n + 1) := by
      field_simp [ne_of_gt hk]
    rw [halg, mul_one_sub_stieltjesChainParameters hk hd n hact]
    exact (hn n hact).symm

/-- Constant diagonal and nonnegative contracted data on the active prefix
give an existential Wall chain representation of the original fraction. -/
theorem exists_chainStieltjes_of_constant_diagonal {kappa : ℝ} (hk : 0 < kappa)
    {a b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hd : ∀ n, (∀ i < n, a i ≠ 0) → stieltjesJacobiDiagonal b n = kappa)
    (hn : ∀ n, (∀ i < n, a i ≠ 0) → stieltjesJacobiNumerator b n = a n) :
    ∃ g : ℕ → ℝ, g 0 = 0 ∧ (∀ n, g n ∈ Set.Icc 0 1) ∧
      stieltjesTail a 0 = stieltjesTail (chainStieltjesNumerators (kappa ^ 2) g) 0 := by
  refine ⟨stieltjesChainParameters kappa a b, rfl,
    stieltjesChainParameters_mem_Icc hk hb hd, ?_⟩
  exact stieltjesTail_eq_of_active_prefix (chainStieltjesNumerators_eq_on_active hk hd hn)

end PowerSeries
