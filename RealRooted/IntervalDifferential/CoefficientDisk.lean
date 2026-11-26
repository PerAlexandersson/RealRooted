/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.CoefficientNorm
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# A root disk from coefficient dominance

Weighted coefficient dominance of a size-reflected polynomial excludes its
complex zeros from the corresponding closed disk.
-/

public section

noncomputable section

open Finset

namespace Polynomial

/-- The weighted coefficient norm bounds evaluation throughout a complex disk. -/
theorem norm_eval₂_le_coefficientNorm {r : ℝ} (p : ℝ[X])
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖p.eval₂ (algebraMap ℝ ℂ) z‖ ≤ coefficientNorm r p := by
  classical
  rw [eval₂_eq_sum, sum_def, coefficientNorm, sum_def]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i _
  simp only [norm_mul, norm_pow, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)

/-- A polynomial whose constant coefficient dominates the others has no zero in
its closed coefficient disk. -/
theorem eval₂_ne_zero_of_coefficientNorm_lt {r : ℝ} (p : ℝ[X])
    (hp : coefficientNorm r (p - C (p.coeff 0)) < |p.coeff 0|)
    {z : ℂ} (hz : ‖z‖ ≤ r) : p.eval₂ (algebraMap ℝ ℂ) z ≠ 0 := by
  intro he
  have hb := norm_eval₂_le_coefficientNorm (p - C (p.coeff 0)) hz
  rw [eval₂_sub, eval₂_C, he, zero_sub, norm_neg, Complex.coe_algebraMap,
    Complex.norm_real, Real.norm_eq_abs] at hb
  exact hp.not_ge hb

/-- Coefficient dominance after reflection puts every root strictly inside the
reciprocal radius. The size parameter can exceed the actual degree. -/
theorem norm_lt_inv_of_reflect_coefficientNorm_lt {r : ℝ} (hr : 0 < r)
    {p : ℝ[X]} {n : ℕ} (hd : p.natDegree ≤ n)
    (hp : coefficientNorm r (reflect n p - C (p.coeff n)) < |p.coeff n|)
    {z : ℂ} (hz : p.eval₂ (algebraMap ℝ ℂ) z = 0) : ‖z‖ < r⁻¹ := by
  by_contra hn
  have hle : r⁻¹ ≤ ‖z‖ := le_of_not_gt hn
  have hz0 : z ≠ 0 := by
    intro he
    have ht : 0 < r⁻¹ := inv_pos.mpr hr
    simp only [he, norm_zero] at hle
    linarith
  have hi : ‖z⁻¹‖ ≤ r := by
    rw [norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr hz0) hr).mpr hle
  have hc : (reflect n p).eval₂ (algebraMap ℝ ℂ) z⁻¹ ≠ 0 := by
    apply eval₂_ne_zero_of_coefficientNorm_lt
    · simpa using hp
    · exact hi
  let _ : Invertible z := invertibleOfNonzero hz0
  apply hc
  simpa only [invOf_eq_inv] using
    (eval₂_reflect_eq_zero_iff (algebraMap ℝ ℂ) z n p hd).mpr hz

end Polynomial
