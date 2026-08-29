import RealRooted.ParkingFunctions.ToricContribution.TriangleAlgebra

/-!
# Diagonal collapse for the toric-contribution triangle

This file conjugates the horizontal insertion operators by powers of `1-X`.
The resulting Euler operators act diagonally on coefficients, reducing the
remaining identification with `R_d` to a finite coefficient identity.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- The shifted Euler operator `(X D + a)`. -/
def eulerShiftOperator (a : ℝ) (f : ℝ[X]) : ℝ[X] :=
  X * f.derivative + C a * f

/-- Successive shifted Euler operators with parameters `c, c+1, ...`. -/
def risingEulerOperator (c : ℝ) : ℕ → ℝ[X] → ℝ[X]
  | 0, f => f
  | t + 1, f => eulerShiftOperator (c + t) (risingEulerOperator c t f)

/-- A shifted Euler operator multiplies coefficient `k` by `k+a`. -/
theorem coeff_eulerShiftOperator (a : ℝ) (f : ℝ[X]) (k : ℕ) :
    (eulerShiftOperator a f).coeff k = (k + a) * f.coeff k := by
  simp only [eulerShiftOperator, coeff_add, coeff_C_mul]
  cases k with
  | zero =>
      simp
  | succ k =>
      rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring

/-- Successive shifted Euler operators multiply coefficient `k` by the rising
factorial `(c+k)_t`. -/
theorem coeff_risingEulerOperator (c : ℝ) (t : ℕ) (f : ℝ[X]) (k : ℕ) :
    (risingEulerOperator c t f).coeff k =
      realRisingFactorial (c + k) t * f.coeff k := by
  induction t with
  | zero => simp [risingEulerOperator]
  | succ t ih =>
      rw [risingEulerOperator, coeff_eulerShiftOperator, ih,
        realRisingFactorial_succ]
      ring

/-- Conjugating one insertion step by powers of `1-X` produces a shifted
Euler operator. -/
theorem one_sub_X_pow_mul_insertionOperator (a : ℝ) (r : ℕ) (f : ℝ[X]) :
    (1 - X) ^ r * insertionOperator a (a + (r + 1)) f =
      eulerShiftOperator a ((1 - X) ^ (r + 1) * f) := by
  simp only [eulerShiftOperator, insertionOperator, intervalWeight,
    derivative_mul, derivative_pow_succ, derivative_sub, derivative_one,
    derivative_X, zero_sub, map_add, map_one, map_natCast]
  ring

/-- The horizontal triangle recursion telescopes to successive Euler
operators after multiplication by the corresponding power of `1-X`. -/
theorem one_sub_X_pow_mul_triangleFamily
    (c : ℝ) (J : ℝ[X]) (d t : ℕ) (ht : t ≤ d) :
    (1 - X) ^ (d + 1 - t) * triangleFamily c J d t =
      risingEulerOperator c t ((1 - X) ^ (d + 1) * (derivative^[d]) J) := by
  induction t with
  | zero => simp [risingEulerOperator]
  | succ t ih =>
      have ht' : t ≤ d := by lia
      rw [show d + 1 - (t + 1) = d - t by lia, triangleFamily_succ]
      have hb : c + d + 1 = (c + t) + (d - t + 1) := by
        ring
      rw [hb, ← Nat.cast_sub ht', one_sub_X_pow_mul_insertionOperator]
      have hexponent : d - t + 1 = d + 1 - t := by lia
      rw [hexponent, ih ht', risingEulerOperator]

/-- At the diagonal, the factor is exactly `1-X`. -/
theorem one_sub_X_mul_triangleFamily_diagonal (c : ℝ) (J : ℝ[X]) (d : ℕ) :
    (1 - X) * triangleFamily c J d d =
      risingEulerOperator c d ((1 - X) ^ (d + 1) * (derivative^[d]) J) := by
  simpa using one_sub_X_pow_mul_triangleFamily c J d d le_rfl

end ToricContribution
end ParkingFunctions
end RealRooted
