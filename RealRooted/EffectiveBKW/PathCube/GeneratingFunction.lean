module

public import RealRooted.EffectiveBKW.PathCube.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The rational generating function of the path-cube rows

The scalar order-four recurrence identifies the series directly, so no determinant
expansion or inverse of a polynomial matrix is needed in the proof.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

open PowerSeries

/-- The quartic denominator of the transfer generating function. -/
noncomputable def denominator (t : ℝ) : PowerSeries ℝ :=
  1 - C (1 + 3 * t) * X ^ 1 - C (2 * t * (1 - t)) * X ^ 2 -
    C (t * (2 - t - t ^ 2)) * X ^ 3 - C (t ^ 2 * (1 - t) ^ 2) * X ^ 4

/-- The cubic numerator of the transfer generating function. -/
noncomputable def numerator (t : ℝ) : PowerSeries ℝ :=
  1 - C (2 * t) * X ^ 1 - C (2 * t) * X ^ 2 - C (t ^ 2 * (1 - t)) * X ^ 3

private theorem coeff_denominator_mul (t : ℝ) (f : PowerSeries ℝ) (n : ℕ) :
    coeff n (denominator t * f) = coeff n f -
      (1 + 3 * t) * (if 1 ≤ n then coeff (n - 1) f else 0) -
      (2 * t * (1 - t)) * (if 2 ≤ n then coeff (n - 2) f else 0) -
      (t * (2 - t - t ^ 2)) * (if 3 ≤ n then coeff (n - 3) f else 0) -
      (t ^ 2 * (1 - t) ^ 2) * (if 4 ≤ n then coeff (n - 4) f else 0) := by
  simp only [denominator, sub_mul, one_mul, mul_assoc, (coeff (R := ℝ) n).map_sub,
    coeff_C_mul, coeff_X_pow_mul']

private theorem coeff_numerator (t : ℝ) (n : ℕ) :
    coeff n (numerator t) = (if n = 0 then 1 else 0) -
      (if n = 1 then 2 * t else 0) - (if n = 2 then 2 * t else 0) -
      (if n = 3 then t ^ 2 * (1 - t) else 0) := by
  simp only [numerator, (coeff (R := ℝ) n).map_sub, coeff_one, coeff_C_mul_X_pow]

/-- The actual matrix-orbit rows satisfy the rational generating-function identity. -/
theorem generating_function (t : ℝ) :
    denominator t * mk (fun r ↦ (row r).eval t) = numerator t := by
  ext n
  rw [coeff_denominator_mul, coeff_numerator]
  match n with
  | 0 => simp
  | 1 => simp; ring
  | 2 =>
    simp [row_two]
    ring
  | 3 =>
    simp [row_two, row_three]
    ring
  | n + 4 =>
    have h := congrArg (Polynomial.eval t) (row_add_four n)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat] at h
    have h₁ : 1 ≤ n + 4 := by lia
    have h₂ : 2 ≤ n + 4 := by lia
    have h₃ : 3 ≤ n + 4 := by lia
    have h₄ : 4 ≤ n + 4 := by lia
    simp [h₁, h₂, h₃, h₄]
    linear_combination h

end RealRooted.EffectiveBKW.PathCube
