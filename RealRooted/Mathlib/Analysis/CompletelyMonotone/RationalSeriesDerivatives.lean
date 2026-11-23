/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.Mathlib.Analysis.CompletelyMonotone.RationalMixtures
import RealRooted.Mathlib.Analysis.CompletelyMonotone.RationalDerivatives
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Ring

/-!
# Differentiation of positive resolvent series

Summability of the nonnegative slopes controls every positive slope power.
The reciprocal denominator is at least one on the nonnegative axis. These
two facts justify termwise differentiation on the open positive half-line.
-/

public section

open Filter Topology

namespace Real

/-- Positive slope-power resolvent series can be differentiated termwise
on the positive half-line, with an explicit summable derivative bound. -/
theorem hasDerivAt_tsum_pow_div_one_add_mul_pow
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (m q : ℕ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ ∑' i, a i ^ (m + 1) / (1 + a i * y) ^ (q + 1))
      (-((q + 1 : ℕ) : ℝ) *
        ∑' i, a i ^ (m + 2) / (1 + a i * x) ^ (q + 2)) x := by
  have hderiv (i : ℕ) (y : ℝ) (hy : y ∈ Set.Ioi (0 : ℝ)) :
      HasDerivAt (fun z : ℝ ↦ a i ^ (m + 1) / (1 + a i * z) ^ (q + 1))
        (-((q + 1 : ℕ) : ℝ) *
          (a i ^ (m + 2) / (1 + a i * y) ^ (q + 2))) y := by
    have hne : 1 + a i * y ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (mul_nonneg (ha i) hy.le))).ne'
    convert hasDerivAt_const_div_one_add_mul_pow (a i) (a i ^ (m + 1)) q hne using 1
    rw [show m + 2 = (m + 1) + 1 by lia, pow_succ]
    ring
  have hbound (i : ℕ) (y : ℝ) (hy : y ∈ Set.Ioi (0 : ℝ)) :
      ‖-((q + 1 : ℕ) : ℝ) *
          (a i ^ (m + 2) / (1 + a i * y) ^ (q + 2))‖ ≤
        ((q + 1 : ℕ) : ℝ) * a i ^ (m + 2) := by
    have hden : 1 ≤ (1 + a i * y) ^ (q + 2) :=
      one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg (ha i) hy.le))
    have hkernel : 0 ≤ a i ^ (m + 2) / (1 + a i * y) ^ (q + 2) :=
      div_nonneg (pow_nonneg (ha i) _) (zero_le_one.trans hden)
    rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (q + 1)), abs_of_nonneg hkernel]
    exact mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg (ha i) _) hden)
      (Nat.cast_nonneg _)
  have hsum : Summable (fun i ↦ ((q + 1 : ℕ) : ℝ) * a i ^ (m + 2)) := by
    simpa only [Nat.add_assoc] using (hs.pow_succ (m + 1)).mul_left ((q + 1 : ℕ) : ℝ)
  have h := hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioi isPreconnected_Ioi
    hderiv hbound (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (TauCeti.summable_const_div_one_add_mul_pow ha (fun i ↦ pow_nonneg (ha i) _)
      (hs.pow_succ m) (q + 1) zero_le_one) hx
  simpa only [tsum_mul_left] using h

/-- Derivatives of a constant plus a positive resolvent sum have the
factorial slope-power representation at every positive argument. -/
theorem iteratedDeriv_const_add_tsum_resolvent
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (gamma : ℝ) (m : ℕ)
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv m (fun y : ℝ ↦ gamma + ∑' i, a i / (1 + a i * y)) x =
      (-1 : ℝ) ^ m * (gamma * 0 ^ m + (m.factorial : ℝ) *
        ∑' i, a i ^ (m + 1) / (1 + a i * x) ^ (m + 1)) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      have heq : iteratedDeriv m (fun y : ℝ ↦ gamma + ∑' i, a i / (1 + a i * y))
          =ᶠ[𝓝 x] (fun y : ℝ ↦ (-1 : ℝ) ^ m * (gamma * 0 ^ m +
            (m.factorial : ℝ) * ∑' i, a i ^ (m + 1) / (1 + a i * y) ^ (m + 1))) :=
        Filter.Eventually.mono
          (isOpen_Ioi.mem_nhds (show x ∈ Set.Ioi (0 : ℝ) from hx)) fun y hy ↦ ih hy
      have hd0 := hasDerivAt_tsum_pow_div_one_add_mul_pow ha hs m m hx
      have hd := HasDerivAt.const_mul ((-1 : ℝ) ^ m)
        ((hd0.const_mul (m.factorial : ℝ)).const_add (gamma * 0 ^ m))
      rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        zero_pow (Nat.succ_ne_zero m), mul_zero, zero_add, pow_succ]
      ring

/-- Alternating signs cancel in the derivative representation, leaving a
nonnegative constant and a positive resolvent series when the data are nonnegative. -/
theorem neg_one_pow_mul_iteratedDeriv_const_add_tsum_resolvent
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (gamma : ℝ) (m : ℕ)
    {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ m *
        iteratedDeriv m (fun y : ℝ ↦ gamma + ∑' i, a i / (1 + a i * y)) x =
      gamma * 0 ^ m + (m.factorial : ℝ) *
        ∑' i, a i ^ (m + 1) / (1 + a i * x) ^ (m + 1) := by
  rw [iteratedDeriv_const_add_tsum_resolvent ha hs gamma m hx, ← mul_assoc, ← mul_pow]
  norm_num

end Real
