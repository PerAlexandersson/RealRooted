/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.CauchyBound

/-!
# Reciprocal-order bounds for infinite differential series

If positive exponents above the two growth orders have reciprocal sum greater
than one, the differential series admits a summable majorant on every spatial
disk. This includes asymmetric order pairs, beyond the case where both orders
are below two.
-/

public section

open Filter Topology

namespace Complex

/-- Cauchy estimates for the two inputs give a reciprocal-power majorant. -/
private theorem exists_differential_rpow_bound {φ f : ℂ → ℂ} {ρ σ p q R : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q) :
    ∃ C > 0, ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤
        C * (Real.exp 2 / ((n : ℝ) + 1) ^ (p⁻¹ + q⁻¹ - 1)) ^ n := by
  obtain ⟨A, hA, ha⟩ := exists_iteratedDeriv_bound_of_orderLE (R := 0) hφ hoφ hp hρ
  obtain ⟨B, hB, hb⟩ := exists_iteratedDeriv_bound_of_orderLE (R := R) hf hof hq hσ
  refine ⟨A * B, mul_pos hA hB, fun n z hz => ?_⟩
  have ha' := ha n 0 (by simp)
  have hb' := hb n z hz
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hfac : (n.factorial : ℝ) ≤ ((n : ℝ) + 1) ^ n := by
    exact_mod_cast (Nat.factorial_le_pow n).trans
      (Nat.pow_le_pow_left (Nat.le_succ n) n)
  have hbase : ((n : ℝ) + 1) *
      (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹ *
        (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) =
      Real.exp 2 / ((n : ℝ) + 1) ^ (p⁻¹ + q⁻¹ - 1) := by
    rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_add (by positivity),
      show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    field_simp
  simp only [norm_div, norm_mul, norm_natCast]
  calc
    _ ≤ ((n.factorial * A * (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹) ^ n) *
        (n.factorial * B * (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹) ^ n)) / n.factorial :=
      div_le_div_of_nonneg_right (mul_le_mul ha' hb' (by positivity) (by positivity))
        (by positivity)
    _ = n.factorial * (A * B) *
        (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹ *
          (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) ^ n := by rw [mul_pow]; field_simp
    _ ≤ ((n : ℝ) + 1) ^ n * (A * B) *
        (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹ *
          (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac (by positivity))
        (by positivity)
    _ = _ := by rw [mul_right_comm, ← mul_pow, hbase, mul_comm]

/-- Positive powers dominating the input orders with reciprocal sum greater
than one give a summable bound for the differential terms on every disk. -/
theorem exists_summable_infiniteDifferentialApply_bound {φ f : ℂ → ℂ} {ρ σ p q R : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤ B n := by
  obtain ⟨C, hC, hbound⟩ := exists_differential_rpow_bound hφ hoφ hp hρ hf hof hq hσ
  refine ⟨fun n => C * (Real.exp 2 / ((n : ℝ) + 1) ^ (p⁻¹ + q⁻¹ - 1)) ^ n, ?_, hbound⟩
  have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (p⁻¹ + q⁻¹ - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlim := htop.const_div_atTop (Real.exp 2)
  apply Summable.of_norm_bounded_eventually_nat
    ((summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left C)
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn.le n) hC.le

end Complex
