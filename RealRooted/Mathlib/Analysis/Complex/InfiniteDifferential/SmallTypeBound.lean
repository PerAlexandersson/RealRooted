/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.ExponentialCoefficients
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.CauchyBound
import RealRooted.Mathlib.Analysis.SpecificLimits.PowerSequence

/-!
# Small exponential-type symbols act close to the identity

A symbol normalized at zero and bounded by `exp (B * norm z)` differs from
the identity operator by at most a constant times `B` on a fixed spatial disk.
The target can be any entire function of finite order, not only an LP function.
-/

public section

namespace Complex

/-- Combine the exponential-type coefficient bound with a finite-order target
jet bound, cancelling only the nonzero factorial denominator. -/
private theorem norm_differential_term_le {φ f : ℂ → ℂ} {B C q : ℝ}
    (hφ : Differentiable ℂ φ) (hB : 0 < B) (hC : 0 < C)
    (hbound : ∀ z, ‖φ z‖ ≤ Real.exp (B * ‖z‖)) (n : ℕ) (z : ℂ)
    (hf : ‖iteratedDeriv n f z‖ ≤ n.factorial * C *
      (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹) ^ n) :
    ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤
      Real.exp 1 * C * (B * (Real.exp 2 / ((n : ℝ) + 1) ^ q⁻¹)) ^ n := by
  have hφn := norm_iteratedDeriv_zero_le_of_exp_norm_bound hφ hB hbound n
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hfac : (n.factorial : ℝ) ≤ ((n : ℝ) + 1) ^ n := by
    exact_mod_cast (Nat.factorial_le_pow n).trans
      (Nat.pow_le_pow_left (Nat.le_succ n) n)
  have hbase : ((n : ℝ) + 1) *
      (Real.exp 1 * B / ((n : ℝ) + 1) *
        (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) =
      B * (Real.exp 2 / ((n : ℝ) + 1) ^ q⁻¹) := by
    rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    field_simp
  simp only [norm_div, norm_mul, norm_natCast]
  calc
    _ ≤ ((n.factorial * Real.exp 1 *
        (Real.exp 1 * B / ((n : ℝ) + 1)) ^ n) *
        (n.factorial * C * (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹) ^ n)) /
        n.factorial :=
      div_le_div_of_nonneg_right
        (mul_le_mul hφn hf (norm_nonneg _) (by positivity)) (by positivity)
    _ = n.factorial * (Real.exp 1 * C) *
        (Real.exp 1 * B / ((n : ℝ) + 1) *
          (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) ^ n := by
      rw [mul_pow]
      field_simp
    _ ≤ ((n : ℝ) + 1) ^ n * (Real.exp 1 * C) *
        (Real.exp 1 * B / ((n : ℝ) + 1) *
          (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac (by positivity))
        (by positivity)
    _ = _ := by rw [mul_right_comm, ← mul_pow, hbase, mul_comm]

/-- Every entire target of finite order admits a diskwise linear bound for
the error made by a normalized symbol of exponential type `0 < B ≤ 1`.
Absolute convergence is proved along with the estimate. -/
theorem exists_infiniteDifferentialApply_sub_bound {f : ℂ → ℂ} {ρ R : ℝ}
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f ρ) :
    ∃ K > 0, ∀ φ : ℂ → ℂ, Differentiable ℂ φ → φ 0 = 1 →
      ∀ B : ℝ, 0 < B → B ≤ 1 →
      (∀ w, ‖φ w‖ ≤ Real.exp (B * ‖w‖)) →
      ∀ z, ‖z‖ ≤ R →
        Summable (fun n : ℕ =>
          ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖) ∧
        ‖infiniteDifferentialApply φ f z - f z‖ ≤ K * B := by
  let q : ℝ := max ρ 0 + 1
  have hq : 0 < q := by dsimp [q]; linarith [le_max_right ρ 0]
  have hρ : ρ < q := by dsimp [q]; linarith [le_max_left ρ 0]
  obtain ⟨C, hC, hc⟩ := exists_iteratedDeriv_bound_of_orderLE
    (R := R) hf hof hq hρ
  let u : ℕ → ℝ := fun n => (Real.exp 2 / ((n : ℝ) + 1) ^ q⁻¹) ^ n
  have hu : Summable u := Real.summable_const_div_rpow_pow (inv_pos.mpr hq) _
  have ht : Summable (fun n => u (n + 1)) := (summable_nat_add_iff 1).mpr hu
  have hun : 0 ≤ ∑' n, u (n + 1) := tsum_nonneg fun n => by dsimp [u]; positivity
  refine ⟨Real.exp 1 * C * ((∑' n, u (n + 1)) + 1), by positivity, ?_⟩
  intro φ hφ hφ0 B hB hB1 hb z hz
  let a : ℕ → ℂ := fun n =>
    iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)
  have ha (n : ℕ) : ‖a (n + 1)‖ ≤ Real.exp 1 * C * B * u (n + 1) := by
    have h := norm_differential_term_le hφ hB hC hb (n + 1) z (hc _ z hz)
    have hpow : B ^ (n + 1) ≤ B := by
      calc
        _ = B ^ n * B := pow_succ _ _
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right (pow_le_one₀ hB.le hB1) hB.le
        _ = B := one_mul _
    apply h.trans
    rw [mul_pow]
    change Real.exp 1 * C * (B ^ (n + 1) * u (n + 1)) ≤
      Real.exp 1 * C * B * u (n + 1)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by dsimp [u]; positivity)
  have htail : Summable (fun n => ‖a (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ha (ht.mul_left _)
  have hall : Summable (fun n => ‖a n‖) := (summable_nat_add_iff 1).mp htail
  refine ⟨hall, ?_⟩
  have heq : infiniteDifferentialApply φ f z - f z = ∑' n, a (n + 1) := by
    change (∑' n, a n) - f z = _
    rw [hall.of_norm.tsum_eq_zero_add]
    simp only [a, iteratedDeriv_zero, hφ0, one_mul, Nat.factorial_zero,
      Nat.cast_one, div_one, add_sub_cancel_left]
  rw [heq]
  calc
    _ ≤ ∑' n, ‖a (n + 1)‖ := norm_tsum_le_tsum_norm htail
    _ ≤ ∑' n, Real.exp 1 * C * B * u (n + 1) :=
      htail.tsum_le_tsum ha (ht.mul_left _)
    _ = Real.exp 1 * C * B * (∑' n, u (n + 1)) := tsum_mul_left
    _ = Real.exp 1 * C * (∑' n, u (n + 1)) * B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hB.le

end Complex
