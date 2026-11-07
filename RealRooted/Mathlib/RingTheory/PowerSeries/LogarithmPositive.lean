/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmMul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic

/-! # Coefficients of logarithms of normalized linear products -/

public section

namespace PowerSeries

/-- The negative logarithm of a normalized negative linear factor has
coefficient `α^n/n` in every positive degree. -/
theorem coeff_neg_logOf_one_sub_C_mul_X (α : ℝ) {n : ℕ} (hn : n ≠ 0) :
    coeff n (-logOf (1 - C α * X : PowerSeries ℝ)) = α ^ n / (n : ℝ) := by
  have harg : (1 - C α * X : PowerSeries ℝ) - 1 = (-α) • X := by
    rw [smul_eq_C_mul, map_neg]
    ring
  rw [map_neg, logOf_eq, harg, ← rescale_eq_subst, coeff_rescale, coeff_log,
    ite_eq_right hn]
  simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
  have hpow : (-α) ^ n = (-1 : ℝ) ^ n * α ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by rw [← mul_pow]; simp
  rw [hpow, pow_succ, div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * (α ^ n * (n : ℝ)⁻¹) := by ring
    _ = _ := by rw [hsign, one_mul]

/-- The negative formal logarithm of a finite normalized linear product has
coefficients given by the power sums of its parameters divided by the degree. -/
theorem coeff_neg_logOf_prod_one_sub_C_mul_X {ι : Type*}
    (s : Finset ι) (α : ι → ℝ) {n : ℕ} (hn : n ≠ 0) :
    coeff n (-logOf (∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ))) =
      (∑ i ∈ s, (α i) ^ n) / (n : ℝ) := by
  rw [logOf_prod s _ (by intro i _; simp), map_neg, map_sum, ← Finset.sum_neg_distrib]
  simp_rw [← map_neg, coeff_neg_logOf_one_sub_C_mul_X _ hn]
  exact (Finset.sum_div _ _ _).symm

/-- Nonempty products of positive linear factors have strictly positive
negative-logarithm coefficients in every positive degree. -/
theorem coeff_neg_logOf_prod_one_sub_C_mul_X_pos {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {n : ℕ} (hn : n ≠ 0) :
    0 < coeff n (-logOf (∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ))) := by
  rw [coeff_neg_logOf_prod_one_sub_C_mul_X s α hn]
  apply div_pos
  · exact Finset.sum_pos (fun i hi ↦ pow_pos (hα i hi) _) hs
  · exact_mod_cast Nat.pos_of_ne_zero hn

end PowerSeries
