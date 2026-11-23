/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Aeration

/-!
# Nonnegative Stieltjes data for translated chain aeration

Alternating `kappa*(1-g_n)` and `kappa*g_(n+1)` contracts to the constant
diagonal `kappa` and outgoing numerators `kappa^2*(1-g_n)*g_(n+1)`.
This gives the formal positivity step in the reverse Wall argument.
-/

public section

namespace PowerSeries

/-- Bounded chain parameters give nonnegative numerators. -/
theorem chainStieltjesNumerators_nonneg {L : ℝ} (hL : 0 ≤ L)
    {g : ℕ → ℝ} (hg : ∀ n, g n ∈ Set.Icc 0 1) (n : ℕ) :
    0 ≤ chainStieltjesNumerators L g n :=
  mul_nonneg (mul_nonneg hL (sub_nonneg.mpr (hg n).2)) (hg (n + 1)).1

/-- Every numerator of a bounded chain is at most its scale. -/
theorem chainStieltjesNumerators_le {L : ℝ} (hL : 0 ≤ L)
    {g : ℕ → ℝ} (hg : ∀ n, g n ∈ Set.Icc 0 1) (n : ℕ) :
    chainStieltjesNumerators L g n ≤ L := by
  calc
    _ ≤ L * (1 - g n) * 1 :=
      mul_le_mul_of_nonneg_left (hg (n + 1)).2 (mul_nonneg hL (sub_nonneg.mpr (hg n).2))
    _ ≤ L := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (sub_le_self 1 (hg n).1) hL

/-- Alternating Stieltjes data for the translated aeration of a chain fraction. -/
@[expose] def chainAerationNumerators (kappa : ℝ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then kappa * (1 - g (n / 2)) else kappa * g (n / 2 + 1)

/-- Even aeration numerators use the complementary chain parameter. -/
@[simp] theorem chainAerationNumerators_even (kappa : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    chainAerationNumerators kappa g (2 * n) = kappa * (1 - g n) := by
  simp [chainAerationNumerators, Nat.mul_comm]

/-- Odd aeration numerators use the next chain parameter. -/
@[simp] theorem chainAerationNumerators_odd (kappa : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    chainAerationNumerators kappa g (2 * n + 1) = kappa * g (n + 1) := by
  simp [chainAerationNumerators, Nat.mul_comm, Nat.add_div]

/-- The alternating data are nonnegative for bounded chain parameters. -/
theorem chainAerationNumerators_nonneg {kappa : ℝ} (hk : 0 ≤ kappa)
    {g : ℕ → ℝ} (hg : ∀ n, g n ∈ Set.Icc 0 1) (n : ℕ) :
    0 ≤ chainAerationNumerators kappa g n := by
  unfold chainAerationNumerators
  split_ifs
  · exact mul_nonneg hk (sub_nonneg.mpr (hg _).2)
  · exact mul_nonneg hk (hg _).1

/-- The contracted diagonal is constant when the initial chain parameter is zero. -/
theorem stieltjesJacobiDiagonal_chainAeration (kappa : ℝ) {g : ℕ → ℝ}
    (hg0 : g 0 = 0) (n : ℕ) :
    stieltjesJacobiDiagonal (chainAerationNumerators kappa g) n = kappa := by
  cases n with
  | zero => simp [stieltjesJacobiDiagonal, chainAerationNumerators, hg0]
  | succ n =>
      change chainAerationNumerators kappa g (2 * n + 1) +
        chainAerationNumerators kappa g (2 * n + 2) = kappa
      rw [show 2 * n + 2 = 2 * (n + 1) by ring,
        chainAerationNumerators_odd, chainAerationNumerators_even]
      ring

/-- The contracted outgoing numerators are exactly the chain numerators. -/
theorem stieltjesJacobiNumerator_chainAeration (kappa : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    stieltjesJacobiNumerator (chainAerationNumerators kappa g) n =
      chainStieltjesNumerators (kappa ^ 2) g n := by
  simp only [stieltjesJacobiNumerator, chainAerationNumerators_even,
    chainAerationNumerators_odd, chainStieltjesNumerators]
  ring

/-- Translated aeration of a chain fraction has explicit nonnegative Stieltjes
data. The formal identity also includes zero shift and terminating fractions. -/
theorem binomialTransform_aerated_chain (kappa : ℝ) {g : ℕ → ℝ} (hg0 : g 0 = 0) :
    binomialTransform kappa
        ((stieltjesTail (chainStieltjesNumerators (kappa ^ 2) g) 0).subst
          (X ^ 2 : ℝ⟦X⟧)) = stieltjesTail (chainAerationNumerators kappa g) 0 := by
  have h : (fun n => binomialTransform kappa
        ((stieltjesTail (chainStieltjesNumerators (kappa ^ 2) g) n).subst
          (X ^ 2 : ℝ⟦X⟧))) = stieltjesJacobiTail (chainAerationNumerators kappa g) := by
    apply eq_of_jacobiStep_eq
    · exact binomialTransform_subst_X_sq_stieltjesTail_eq_step kappa
        (chainStieltjesNumerators (kappa ^ 2) g)
    · intro n
      rw [stieltjesJacobiTail_eq_step, stieltjesJacobiDiagonal_chainAeration kappa hg0,
        stieltjesJacobiNumerator_chainAeration]
  exact congrFun h 0

end PowerSeries
