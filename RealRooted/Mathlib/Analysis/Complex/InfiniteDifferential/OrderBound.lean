/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.CauchyBound
import RealRooted.Mathlib.Analysis.SpecificLimits.PowerSequence

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

/-- The differential terms have a reciprocal-power majorant with explicit
exponential dependence on the spatial point. -/
theorem exists_infiniteDifferentialApply_term_bound_of_order {φ f : ℂ → ℂ}
    {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q) :
    ∃ C > 0, ∀ n : ℕ, ∀ z : ℂ,
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤
        C * Real.exp (‖z‖ ^ q) * (Real.exp 2 / ((n : ℝ) + 1) ^ (p⁻¹ + q⁻¹ - 1)) ^ n := by
  obtain ⟨A, hA, ha⟩ := exists_iteratedDeriv_global_bound_of_orderLE hφ hoφ hp hρ
  obtain ⟨B, hB, hb⟩ := exists_iteratedDeriv_global_bound_of_orderLE hf hof hq hσ
  refine ⟨A * B, mul_pos hA hB, fun n z => ?_⟩
  have ha' : ‖iteratedDeriv n φ 0‖ ≤ n.factorial * A *
      (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹) ^ n := by
    simpa only [norm_zero, Real.zero_rpow hp.ne', Real.exp_zero, mul_one] using ha n 0
  have hb' := hb n z
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
        (n.factorial * B * Real.exp (‖z‖ ^ q) *
          (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹) ^ n)) / n.factorial :=
      div_le_div_of_nonneg_right (mul_le_mul ha' hb' (by positivity) (by positivity))
        (by positivity)
    _ = n.factorial * (A * B * Real.exp (‖z‖ ^ q)) *
        (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹ *
          (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) ^ n := by rw [mul_pow]; field_simp
    _ ≤ ((n : ℝ) + 1) ^ n * (A * B * Real.exp (‖z‖ ^ q)) *
        (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹ *
          (Real.exp 1 / ((n : ℝ) + 1) ^ q⁻¹)) ^ n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac (by positivity))
        (by positivity)
    _ = _ := by rw [mul_right_comm, ← mul_pow, hbase, mul_comm]

/-- Restricting the global majorant to a disk gives a fixed spatial constant. -/
private theorem exists_differential_rpow_bound {φ f : ℂ → ℂ} {ρ σ p q R : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q) :
    ∃ C > 0, ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤
        C * (Real.exp 2 / ((n : ℝ) + 1) ^ (p⁻¹ + q⁻¹ - 1)) ^ n := by
  obtain ⟨C, hC, hbound⟩ := exists_infiniteDifferentialApply_term_bound_of_order
    hφ hoφ hp hρ hf hof hq hσ
  refine ⟨C * Real.exp (R ^ q), by positivity, fun n z hz => (hbound n z).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (Real.rpow_le_rpow (norm_nonneg _) hz hq.le)) hC.le) (by positivity)

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
  exact (Real.summable_const_div_rpow_pow (by linarith : 0 < p⁻¹ + q⁻¹ - 1)
    (Real.exp 2)).mul_left C

end Complex
