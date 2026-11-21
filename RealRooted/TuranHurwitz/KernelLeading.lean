module

public import RealRooted.TuranHurwitz.DiskCoefficients
public import RealRooted.TuranHurwitz.IntervalOperator
import RealRooted.TuranHurwitz.TanhCoefficients
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform lower bounds on kernel leading coefficients

These bounds remain useful when the normalized exponent tends to infinity.
They do not require any restriction on the fixed complex root parameters.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The exact leading-coefficient recurrence for the interval rows. -/
theorem intervalRow_leadingCoeff_succ {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (intervalRow d (n + 1)).leadingCoeff =
      (2 * n + 1) * (2 * n + 2 * d) * (intervalRow d n).leadingCoeff := by
  have hp : intervalRow d n ≠ 0 :=
    leadingCoeff_ne_zero.mp (intervalRow_natDegree_and_leadingCoeff_pos hd n).2.ne'
  rw [intervalRow, leadingCoeff_mul, leadingCoeff_X, one_mul, ← coeff_natDegree,
    intervalOperator_natDegree hd hp, coeff_intervalOperator_natDegree,
    (intervalRow_natDegree_and_leadingCoeff_pos hd n).1]

/-- A coarse pure-power lower bound for the interval-row leader. -/
theorem pow_le_intervalRow_leadingCoeff {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (2 * d) ^ n ≤ (intervalRow d n).leadingCoeff := by
  induction n with
  | zero => simp [intervalRow]
  | succ n ih =>
      rw [intervalRow_leadingCoeff_succ hd, pow_succ]
      have hfactor : 2 * d ≤ (2 * n + 1) * (2 * n + 2 * d) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      calc
        _ ≤ (intervalRow d n).leadingCoeff * (2 * d) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ _ := by
          rw [mul_comm (intervalRow d n).leadingCoeff]
          exact mul_le_mul_of_nonneg_right hfactor
            (intervalRow_natDegree_and_leadingCoeff_pos hd n).2.le

/-- Translation does not change the base tanh coefficient's leader. -/
theorem leadingCoeff_coeff_even_tanhKernel (d : ℝ) (n : ℕ) :
    (PowerSeries.coeff (2 * n) (tanhKernel d)).leadingCoeff =
      (((2 * n).factorial : ℝ)⁻¹) * (intervalRow d n).leadingCoeff := by
  rw [coeff_even_tanhKernel, leadingCoeff_comp
    (show (X - 1 : ℝ[X]).natDegree ≠ 0 by
      rw [show (X - 1 : ℝ[X]) = X - C (1 : ℝ) by simp, natDegree_X_sub_C]
      exact one_ne_zero),
    show (X - 1 : ℝ[X]).leadingCoeff = 1 by simpa using leadingCoeff_X_sub_C (1 : ℝ)]
  simp only [one_pow, mul_one, coeff_even_hyperbolicKernel, leadingCoeff_mul, leadingCoeff_C]

/-- The complex base leader is the scalar extension of the positive real leader. -/
theorem leadingCoeff_diskCoefficient_zero (d : ℝ) (eta : ℕ → ℂ) (n : ℕ) :
    (diskCoefficient d eta n 0).leadingCoeff =
      (((((2 * n).factorial : ℝ)⁻¹) * (intervalRow d n).leadingCoeff : ℝ) : ℂ) := by
  rw [diskCoefficient_zero,
    leadingCoeff_map_of_injective (algebraMap ℝ ℂ).injective,
    leadingCoeff_coeff_even_tanhKernel]
  rfl

/-- Kernel induction never decreases the norm of the leading coefficient. -/
theorem norm_leadingCoeff_diskCoefficient_step {d : ℝ} (hd : 0 < d) (eta : ℕ → ℂ)
    (n ell : ℕ) (hp : diskCoefficient d eta n ell ≠ 0) :
    ‖(diskCoefficient d eta n ell).leadingCoeff‖ ≤
      ‖(diskCoefficient d eta n (ell + 1)).leadingCoeff‖ := by
  have ha : 0 < d + (ell : ℝ) := add_pos_of_pos_of_nonneg hd (Nat.cast_nonneg _)
  rw [diskCoefficient_succ hd, (diskStep_natDegree_and_leadingCoeff ha _ hp).2, norm_mul]
  have hc : ‖(1 + ((diskCoefficient d eta n ell).natDegree : ℂ) /
      ((d + ell : ℝ) : ℂ))‖ =
      1 + ((diskCoefficient d eta n ell).natDegree : ℝ) / (d + ell) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_one,
      ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [hc]
  have hnn := div_nonneg (Nat.cast_nonneg (α := ℝ)
    (diskCoefficient d eta n ell).natDegree) ha.le
  nlinarith [norm_nonneg (diskCoefficient d eta n ell).leadingCoeff]

/-- The norm of every disk coefficient's leader has a uniform positive power lower bound. -/
theorem pow_div_factorial_le_norm_leadingCoeff_diskCoefficient {d : ℝ} (hd : 0 < d)
    (eta : ℕ → ℂ) (heta : ∀ j, ‖eta j‖ ≤ 1) (n ell : ℕ) :
    (2 * d) ^ n / ((2 * n).factorial : ℝ) ≤
      ‖(diskCoefficient d eta n ell).leadingCoeff‖ := by
  induction ell with
  | zero =>
      rw [leadingCoeff_diskCoefficient_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (intervalRow_natDegree_and_leadingCoeff_pos hd n).2.le)]
      rw [div_eq_mul_inv, mul_comm _ ((intervalRow d n).leadingCoeff)]
      exact mul_le_mul_of_nonneg_right (pow_le_intervalRow_leadingCoeff hd n)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
  | succ ell ih =>
      exact ih.trans (norm_leadingCoeff_diskCoefficient_step hd eta n ell
        (diskCoefficient_degree_and_roots hd eta heta n ell).1)

end RealRooted.TuranHurwitz
