module

public import RealRooted.TuranHurwitz.Recurrence
public import RealRooted.TuranHurwitz.FlowShift
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Turán sums as formal paired coefficients

The Cauchy product identity applies to any real polynomial sequence.
For the normalized recurrence the formal flow supplies its shifted series.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The shifted exponential generating series of a polynomial sequence evaluated at `u`. -/
@[expose] noncomputable def shiftedSeries (P : ℕ → ℝ[X]) (m : ℕ) (u : ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk fun k => Polynomial.aeval u (P (m + k)) / (k.factorial : ℂ)

/-- The flow realizes the shifted exponential generating series coefficientwise. -/
theorem flowRow_eq_shiftedSeries (d h : ℝ) (u : ℂ) (m : ℕ) :
    flowRow d h u m = shiftedSeries (normalized d h) m u := by
  apply PowerSeries.ext
  intro k
  rw [shiftedSeries, PowerSeries.coeff_mk, coeff_flowRow]

/-- The paired coefficient is the extended Turán sum with its conventional sign. -/
theorem coeff_paired_shiftedSeries (P : ℕ → ℝ[X]) (m n : ℕ) (u : ℂ) :
    PowerSeries.coeff (2 * n) (shiftedSeries P m u *
      PowerSeries.rescale (-1) (shiftedSeries P m u)) =
      (-1 : ℂ) ^ n * Polynomial.aeval u (turan m n P) := by
  rw [mul_comm (shiftedSeries P m u), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_rescale, shiftedSeries, PowerSeries.coeff_mk]
  rw [turan, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ 2 * n := by simpa using (Finset.mem_range.mp hj)
  have hindex : m + (2 * n - j) = m + 2 * n - j := by lia
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ (n + j) = (-1 : ℂ) ^ j := by
    have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; simp
    rw [pow_add, ← mul_assoc, hs, one_mul]
  simp only [map_mul, Polynomial.aeval_C]
  simp only [map_div₀, map_pow, map_neg, map_one, map_mul, map_natCast]
  rw [hindex]
  simp only [div_eq_mul_inv, mul_inv_rev]
  linear_combination -hsign *
    ((j.factorial : ℂ)⁻¹ * ((2 * n - j).factorial : ℂ)⁻¹ *
      Polynomial.aeval u (P (m + j)) * Polynomial.aeval u (P (m + 2 * n - j)))

/-- The normalized Turán sum is the paired coefficient of the actual formal flow. -/
theorem coeff_paired_flowRow (d h : ℝ) (u : ℂ) (m n : ℕ) :
    PowerSeries.coeff (2 * n)
      (flowRow d h u m * PowerSeries.rescale (-1) (flowRow d h u m)) =
      (-1 : ℂ) ^ n * Polynomial.aeval u (turan m n (normalized d h)) := by
  rw [flowRow_eq_shiftedSeries]
  exact coeff_paired_shiftedSeries _ m n u

end RealRooted.TuranHurwitz
