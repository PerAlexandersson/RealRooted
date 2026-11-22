/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.ExponentialPowerBound

/-!
# Cauchy derivative estimates above the growth order

A circle of radius `(n+1)^(1/p)` bounds the nth derivative when the entire
function has growth order strictly below the positive exponent `p`.
The estimate is uniform on each spatial disk.
-/

public section

open Metric

namespace Complex

/-- A nonnegative real power of a sum is bounded by a convenient multiple of
the sum of the powers, including exponents below one. -/
private theorem add_rpow_le_two_mul {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ p * (a ^ p + b ^ p) := by
  calc
    _ ≤ (2 * max a b) ^ p :=
      Real.rpow_le_rpow (add_nonneg ha hb) (by linarith [le_max_left a b, le_max_right a b]) hp
    _ = (2 : ℝ) ^ p * max (a ^ p) (b ^ p) := by
      rw [Real.mul_rpow (by positivity) (ha.trans (le_max_left _ _)), Real.rpow_max ha hb hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right (Real.rpow_nonneg hb _))
        (le_add_of_nonneg_left (Real.rpow_nonneg ha _))) (by positivity)

/-- Above a positive growth exponent, Cauchy's estimate gives a common
factorial and reciprocal-power bound for every derivative on a spatial disk. -/
theorem exists_iteratedDeriv_bound_of_orderLE {f : ℂ → ℂ} {ρ p R : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ)
    (hp : 0 < p) (hρ : ρ < p) :
    ∃ C > 0, ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖iteratedDeriv n f z‖ ≤ n.factorial * C *
        (Real.exp 1 / ((n : ℝ) + 1) ^ p⁻¹) ^ n := by
  let ε := ((2 : ℝ) ^ p)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hbound⟩ := horder.exists_norm_le_mul_exp_rpow hf.continuous hp hρ hε
  refine ⟨C * Real.exp (R ^ p + 1), by positivity, fun n z hz => ?_⟩
  let r : ℝ := ((n : ℝ) + 1) ^ p⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hrp : r ^ p = (n : ℝ) + 1 := Real.rpow_inv_rpow (by positivity) hp.ne'
  have hcircle : ∀ w ∈ sphere z r,
      ‖f w‖ ≤ C * Real.exp (R ^ p + 1 + (n : ℝ)) := by
    intro w hw
    have hwz : ‖w - z‖ = r := mem_sphere_iff_norm.mp hw
    have htri := norm_add_le (w - z) z
    rw [sub_add_cancel, hwz] at htri
    have hwbound : ‖w‖ ^ p ≤ (2 : ℝ) ^ p * (R ^ p + ((n : ℝ) + 1)) := by
      calc
        _ ≤ (‖z‖ + r) ^ p := Real.rpow_le_rpow (norm_nonneg _) (by linarith) hp.le
        _ ≤ (2 : ℝ) ^ p * (‖z‖ ^ p + r ^ p) :=
          add_rpow_le_two_mul (norm_nonneg _) hr.le hp.le
        _ ≤ _ := by
          rw [hrp]
          exact mul_le_mul_of_nonneg_left
            (add_le_add (Real.rpow_le_rpow (norm_nonneg _) hz hp.le) le_rfl) (by positivity)
    apply (hbound w).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ε * ((2 : ℝ) ^ p * (R ^ p + ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hwbound hε.le
      _ = _ := by dsimp [ε]; field_simp; ring
  have hcauchy := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hf.diffContOnCl hcircle
  convert hcauchy using 1
  rw [Real.exp_add (R ^ p + 1) (n : ℝ), ← Real.exp_one_pow, div_pow]
  dsimp only [r]
  ring

end Complex
