/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import RealRooted.Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianTail

/-!
# Differentiating polynomially weighted Gaussian lattice series in the width
-/

public section

open Set

namespace Real

/-- Positive-index polynomial Gaussian series converge for every positive width. -/
theorem summable_pow_mul_exp_neg_sq_parameter (q : ℕ) {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ q * exp (-c * (n + 1 : ℝ) ^ 2 * t)) := by
  have h := (summable_nat_add_iff 1).mpr
    (summable_nat_pow_mul_exp_neg_sq q (mul_pos hc ht))
  convert h using 1
  funext n
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2
  ring

private theorem hasDerivAt_gaussian_weight (q n : ℕ) (c t : ℝ) :
    HasDerivAt (fun y : ℝ => (n + 1 : ℝ) ^ q * exp (-c * (n + 1 : ℝ) ^ 2 * y))
      (-c * ((n + 1 : ℝ) ^ (q + 2) * exp (-c * (n + 1 : ℝ) ^ 2 * t))) t := by
  convert (((hasDerivAt_id t).const_mul (-c * (n + 1 : ℝ) ^ 2)).exp).const_mul
    ((n + 1 : ℝ) ^ q) using 1
  · simp only [id_eq]
  · simp only [id_eq, mul_one, pow_add]
    ring

private theorem norm_gaussian_weight_le (q n : ℕ) {c t y : ℝ}
    (hc : 0 < c) (hy : t / 2 < y) :
    ‖-c * ((n + 1 : ℝ) ^ (q + 2) * exp (-c * (n + 1 : ℝ) ^ 2 * y))‖ ≤
      c * ((n + 1 : ℝ) ^ (q + 2) * exp (-c * (n + 1 : ℝ) ^ 2 * (t / 2))) := by
  rw [norm_mul, norm_neg, norm_of_nonneg hc.le, norm_mul,
    norm_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ) ^ (q + 2)), norm_of_nonneg (exp_pos _).le]
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hy.le
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _))

/-- The actual width derivative increases the polynomial weight by two. -/
theorem hasDerivAt_tsum_pow_mul_exp_neg_sq_parameter (q : ℕ) {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => ∑' n : ℕ, (n + 1 : ℝ) ^ q *
      exp (-c * (n + 1 : ℝ) ^ 2 * y))
      (-c * ∑' n : ℕ, (n + 1 : ℝ) ^ (q + 2) * exp (-c * (n + 1 : ℝ) ^ 2 * t)) t := by
  have hM := (summable_pow_mul_exp_neg_sq_parameter (q + 2) hc (half_pos ht)).mul_left c
  have hmem : t ∈ Ioi (t / 2) := by change t / 2 < t; linarith
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioi isPreconnected_Ioi
    (fun n y _ => hasDerivAt_gaussian_weight q n c y)
    (fun n y hy => norm_gaussian_weight_le q n hc hy) hmem
    (summable_pow_mul_exp_neg_sq_parameter q hc ht) hmem
  simpa only [tsum_mul_left] using h

end Real
