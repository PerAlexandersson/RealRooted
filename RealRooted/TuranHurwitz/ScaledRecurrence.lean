module

public import RealRooted.TuranHurwitz.FlowShift
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Formal transport of the normalized recurrence

Three algebraic identities for the scale and transformed argument imply
the original differential recurrence. Multiplying once by the scale avoids
division by powers and handles the zeroth row uniformly.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Multiplying a differentiated power by its base removes the predecessor exponent. -/
theorem mul_derivative_series_pow (F : PowerSeries ℂ) (j : ℕ) :
    F * PowerSeries.derivative (F ^ j) =
      PowerSeries.C (j : ℂ) * PowerSeries.derivative F * F ^ j := by
  cases j with
  | zero => simp
  | succ j =>
      rw [PowerSeries.derivative_pow]
      simp only [Nat.add_sub_cancel, map_natCast, Nat.cast_add, Nat.cast_one,
        map_add, map_one]
      rw [pow_succ]
      ring

/-- The three scale identities transport the normalized polynomial recurrence. -/
theorem scaled_normalized_succ (d h : ℝ) (F U A L Q : PowerSeries ℂ) (hF : F ≠ 0)
    (hA : F * (PowerSeries.C (d : ℂ) * U + PowerSeries.C (h : ℂ)) = A)
    (hL : F * L + Q * PowerSeries.derivative F = 0)
    (hU : F * (U ^ 2 - 1) = Q * PowerSeries.derivative U) (j : ℕ) :
    F ^ (j + 1) * Polynomial.aeval U (normalized d h (j + 1)) =
      (A + PowerSeries.C (j : ℂ) * L) * (F ^ j * Polynomial.aeval U (normalized d h j)) +
        Q * PowerSeries.derivative (F ^ j * Polynomial.aeval U (normalized d h j)) := by
  apply mul_left_cancel₀ hF
  rw [normalized_succ, PowerSeries.derivative.leibniz, derivative_aeval_series]
  have hc (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
  simp only [map_add, map_mul, map_sub, map_pow, map_one, Polynomial.aeval_X,
    Polynomial.aeval_C, PowerSeries.algebraMap_apply, hc, smul_eq_mul]
  have hpow := mul_derivative_series_pow F j
  linear_combination
    (F ^ (j + 1) * Polynomial.aeval U (normalized d h j)) * hA +
    (F ^ (j + 1) * Polynomial.aeval U (normalized d h j).derivative) * hU -
    (PowerSeries.C (j : ℂ) * F ^ j * Polynomial.aeval U (normalized d h j)) * hL -
    (Q * Polynomial.aeval U (normalized d h j)) * hpow

end RealRooted.TuranHurwitz
