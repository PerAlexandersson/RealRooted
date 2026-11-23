/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.Mathlib.Analysis.CompletelyMonotone.RationalMixtures
import RealRooted.Mathlib.Analysis.CompletelyMonotone.RationalSeriesDerivatives
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The positive resolvent hierarchy

The factorial resolvent kernels satisfy both ordinary derivative and Euler
recurrences. These identities connect the positive-series representation to
Zhang's two-index differential family, including its exponential boundary.
-/

public section

namespace Real

/-- The factorial resolvent family associated with summable linear slopes
and a constant logarithmic derivative. The parameters are not assumed positive
in the definition; positivity is required by its complete-monotonicity theorem. -/
@[expose] noncomputable def weightedResolventSum
    (a : ℕ → ℝ) (gamma : ℝ) (k m : ℕ) (x : ℝ) : ℝ :=
  (k.factorial : ℝ) * gamma * 0 ^ m +
    ((k + m).factorial : ℝ) *
      ∑' i, a i ^ (m + 1) / (1 + a i * x) ^ (k + m + 1)

/-- Every member of the positive resolvent hierarchy is completely monotone. -/
theorem isCompletelyMonotoneOnIoi_weightedResolventSum
    {a : ℕ → ℝ} {gamma : ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (hg : 0 ≤ gamma) (k m : ℕ) :
    TauCeti.IsCompletelyMonotoneOnIoi (weightedResolventSum a gamma k m) :=
  TauCeti.isCompletelyMonotoneOnIoi_factorial_resolvent_sum ha hs hg k m

/-- Differentiation increases the second index of the resolvent hierarchy
and changes its sign. -/
theorem hasDerivAt_weightedResolventSum
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (gamma : ℝ) (k m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (weightedResolventSum a gamma k m)
      (-weightedResolventSum a gamma k (m + 1) x) x := by
  have hd0 := hasDerivAt_tsum_pow_div_one_add_mul_pow ha hs m (k + m) hx
  have hd := (hd0.const_mul ((k + m).factorial : ℝ)).const_add
    ((k.factorial : ℝ) * gamma * 0 ^ m)
  dsimp only [weightedResolventSum]
  apply hd.congr_deriv
  rw [show k + (m + 1) = k + m + 1 by lia, Nat.factorial_succ, Nat.cast_mul]
  simp only [Nat.add_assoc, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_add]
  ring

/-- The denominator cancellation for positive resolvent series. -/
private theorem tsum_resolvent_sub_mul_tsum
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (m q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' i, a i ^ (m + 1) / (1 + a i * x) ^ (q + 1)) -
        x * (∑' i, a i ^ (m + 2) / (1 + a i * x) ^ (q + 2)) =
      ∑' i, a i ^ (m + 1) / (1 + a i * x) ^ (q + 2) := by
  have h₁ := TauCeti.summable_const_div_one_add_mul_pow
    ha (fun i ↦ pow_nonneg (ha i) _) (hs.pow_succ m) (q + 1) hx
  have h₂ : Summable (fun i ↦ a i ^ (m + 2) / (1 + a i * x) ^ (q + 2)) := by
    simpa only [Nat.add_assoc] using TauCeti.summable_const_div_one_add_mul_pow
      ha (fun i ↦ pow_nonneg (ha i) _) (hs.pow_succ (m + 1)) (q + 2) hx
  calc
    _ = ∑' i, (a i ^ (m + 1) / (1 + a i * x) ^ (q + 1) -
        x * (a i ^ (m + 2) / (1 + a i * x) ^ (q + 2))) := by
      rw [h₁.tsum_sub (h₂.mul_left x), tsum_mul_left]
    _ = _ := by
      apply tsum_congr
      intro i
      have hne : 1 + a i * x ≠ 0 :=
        (lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_right (mul_nonneg (ha i) hx))).ne'
      field_simp [hne, pow_succ]
      ring

/-- The Euler recurrence for the resolvent hierarchy. Its constant term
also satisfies the recurrence, including when the first index is zero. -/
theorem mul_weightedResolventSum_add_mul_deriv
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (gamma : ℝ) (k m : ℕ) {x : ℝ} (hx : 0 < x) :
    ((m + k + 1 : ℕ) : ℝ) * weightedResolventSum a gamma k m x +
        x * deriv (weightedResolventSum a gamma k m) x =
      weightedResolventSum a gamma (k + 1) m x := by
  rw [(hasDerivAt_weightedResolventSum ha hs gamma k m hx).deriv]
  let S : ℕ → ℕ → ℝ := fun p q ↦
    ∑' i, a i ^ (p + 1) / (1 + a i * x) ^ (q + 1)
  have hsum : S m (k + m) - x * S (m + 1) (k + m + 1) = S m (k + m + 1) := by
    simpa only [S, Nat.add_assoc] using tsum_resolvent_sub_mul_tsum ha hs m (k + m) hx.le
  have hconstant :
      ((m + k + 1 : ℕ) : ℝ) * ((k.factorial : ℝ) * gamma * 0 ^ m) =
        ((k + 1).factorial : ℝ) * gamma * 0 ^ m := by
    cases m with
    | zero => simp [Nat.factorial_succ, mul_assoc]
    | succ m => simp
  have hfactorial : ((k + m + 1).factorial : ℝ) =
      ((m + k + 1 : ℕ) : ℝ) * ((k + m).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    congr 1
    exact_mod_cast (show k + m + 1 = m + k + 1 by lia)
  simp only [weightedResolventSum, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_add]
  rw [show k + (m + 1) = k + m + 1 by lia,
    show (k + 1) + m = k + m + 1 by lia]
  change ((m + k + 1 : ℕ) : ℝ) *
      ((k.factorial : ℝ) * gamma * 0 ^ m + ((k + m).factorial : ℝ) * S m (k + m)) +
      x * (-(((k + m + 1).factorial : ℝ) * S (m + 1) (k + m + 1))) =
    ((k + 1).factorial : ℝ) * gamma * 0 ^ m +
      ((k + m + 1).factorial : ℝ) * S m (k + m + 1)
  calc
    _ = ((m + k + 1 : ℕ) : ℝ) * ((k.factorial : ℝ) * gamma * 0 ^ m) +
        ((k + m + 1).factorial : ℝ) *
          (S m (k + m) - x * S (m + 1) (k + m + 1)) := by rw [hfactorial]; ring
    _ = _ := by rw [hconstant, hsum]

/-- The zeroth Euler row is the alternating derivative of the associated
constant-plus-resolvent logarithmic derivative. -/
theorem weightedResolventSum_zero_eq_signed_deriv
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (gamma : ℝ) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    weightedResolventSum a gamma 0 m x =
      (-1 : ℝ) ^ m *
        iteratedDeriv m (fun y : ℝ ↦ gamma + ∑' i, a i / (1 + a i * y)) x := by
  simpa only [weightedResolventSum, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add]
    using (neg_one_pow_mul_iteratedDeriv_const_add_tsum_resolvent ha hs gamma m hx).symm

end Real
