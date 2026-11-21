/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RealRooted.CombinatorialExamples.CaoFu.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# A cubic bound for the complex sine

This supplies the elementary sine estimate in the centered-disk route to
Cao--Fu, arXiv:2610.40496v1, Theorem 1.1. We bound the absolutely convergent
sine series by the hyperbolic sine series, then dominate its tail geometrically.
The cosecant partial-fraction representation is not assumed or proved here.
-/

public section

namespace RealRooted.CaoFu

/-- The complex sine is bounded by the hyperbolic sine of its norm. -/
theorem norm_sin_le_sinh_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := by
  have hnorm : ∀ n : ℕ,
      ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)‖ =
        ‖z‖ ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
    intro n
    simp
  have hsum : Summable (fun n : ℕ =>
      ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)‖) := by
    simpa only [hnorm] using (Real.hasSum_sinh ‖z‖).summable
  rw [Complex.sin_eq_tsum]
  calc
    _ ≤ ∑' n : ℕ,
        ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ = Real.sinh ‖z‖ := by simp only [hnorm, ← Real.sinh_eq_tsum]

/-- A factorial lower bound for the tail of the hyperbolic sine series. -/
private theorem factorial_tail_le (n : ℕ) :
    (6 : ℝ) * 20 ^ n ≤ ((2 * n + 3).factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hidx : 2 * (n + 1) + 3 = (2 * n + 3) + 1 + 1 := by lia
    rw [hidx, Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
    have hfactor : (20 : ℝ) ≤ ((2 * n + 3 + 1 + 1 : ℕ) : ℝ) *
        ((2 * n + 3 + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hnonneg : (0 : ℝ) ≤ (2 * n + 3).factorial := Nat.cast_nonneg _
    have hm := mul_le_mul hfactor ih (by positivity) (by positivity)
    rw [pow_succ]
    nlinarith

/-- A geometric tail bound for the hyperbolic sine on the required radius. -/
theorem sinh_le_cubic_of_sq_le {x : ℝ} (hx : 0 ≤ x) (hx₂ : x ^ 2 ≤ 10 / 3) :
    Real.sinh x ≤ x * (1 + x ^ 2 / 5) := by
  have hratio : |x ^ 2 / 20| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hgeo := (hasSum_geometric_of_abs_lt_one hratio).mul_left (x ^ 3 / 6)
  have hsum := (Real.hasSum_sinh x).summable
  have htail : Summable (fun n : ℕ => x ^ (2 * (n + 1) + 1) /
      ((2 * (n + 1) + 1).factorial : ℝ)) := (summable_nat_add_iff 1).mpr hsum
  have hterm (n : ℕ) : x ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1).factorial : ℝ) ≤
      x ^ 3 / 6 * (x ^ 2 / 20) ^ n := by
    have hfac := factorial_tail_le n
    have hidx : 2 * (n + 1) + 1 = 2 * n + 3 := by lia
    rw [hidx]
    calc
      _ ≤ x ^ (2 * n + 3) / (6 * 20 ^ n) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = _ := by rw [pow_add, pow_mul, div_pow]; ring
  have hle := htail.tsum_le_tsum hterm hgeo.summable
  rw [hgeo.tsum_eq] at hle
  have hsplit := hsum.tsum_eq_zero_add
  rw [← Real.sinh_eq_tsum] at hsplit
  simp only [Nat.mul_zero, zero_add, pow_one, Nat.factorial_one, Nat.cast_one,
    div_one] at hsplit
  have hden : 0 < 1 - x ^ 2 / 20 := by linarith
  have hnum : (x ^ 3 / 6) * (1 - x ^ 2 / 20)⁻¹ ≤ x ^ 3 / 5 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hden]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx₂)]
  nlinarith

/-- The complex sine estimate used in Lemma D of the centered crown proof. -/
theorem norm_sin_le_cubic (z : ℂ) (hz : ‖z‖ ^ 2 ≤ 10 / 3) :
    ‖Complex.sin z‖ ≤ ‖z‖ * (1 + ‖z‖ ^ 2 / 5) :=
  (norm_sin_le_sinh_norm z).trans (sinh_le_cubic_of_sq_le (norm_nonneg _) hz)

/-- The inverse squared sine has the uniform linear lower bound required by Lemma D. -/
theorem mul_le_inv_norm_sin_sq {w : ℝ} (hw : 13 / 3 ≤ w) (z : ℂ)
    (hz : ‖z‖ ^ 2 = Real.pi ^ 2 / (4 * w)) (hsin : Complex.sin z ≠ 0) :
    (1633 / 5000 : ℝ) * w ≤ ‖Complex.sin z‖⁻¹ ^ 2 := by
  have hw0 : 0 < w := by linarith
  have hrad : ‖z‖ ^ 2 ≤ 3 * Real.pi ^ 2 / 52 := by
    rw [hz, div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left hw (sq_nonneg Real.pi)
    nlinarith
  have hsinBound := norm_sin_le_cubic z (hrad.trans pi_sq_radius_le)
  have hfactor : 1 + ‖z‖ ^ 2 / 5 ≤ 1 + 3 * Real.pi ^ 2 / 260 := by linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg (Complex.sin z)) hsinBound 2
  have hfactorSq := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖z‖ ^ 2 / 5) hfactor 2)
    (sq_nonneg ‖z‖)
  have hupper : ‖Complex.sin z‖ ^ 2 ≤ ‖z‖ ^ 2 * (1 + 3 * Real.pi ^ 2 / 260) ^ 2 := by
    nlinarith
  have heq : ‖z‖ ^ 2 * (4 * w) = Real.pi ^ 2 :=
    (eq_div_iff (by positivity : 4 * w ≠ 0)).mp hz
  have hscaled : ‖Complex.sin z‖ ^ 2 * (4 * w) ≤
      Real.pi ^ 2 * (1 + 3 * Real.pi ^ 2 / 260) ^ 2 := by
    calc
      _ ≤ (‖z‖ ^ 2 * (1 + 3 * Real.pi ^ 2 / 260) ^ 2) * (4 * w) :=
        mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = _ := by rw [mul_right_comm, heq]
  have hpi := Real.pi_pos
  have hconstant := (le_div_iff₀ (by positivity :
    0 < Real.pi ^ 2 * (1 + 3 * Real.pi ^ 2 / 260) ^ 2)).mp sine_bound_constant_le
  have hpos : 0 < ‖Complex.sin z‖ ^ 2 := by positivity
  rw [inv_pow, inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith

end RealRooted.CaoFu
