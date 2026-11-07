module

public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-! Differential equations imply the finite coefficient recurrence used in
the weighted Hessenberg determinant identity. -/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Multiplication by the variable turns formal differentiation into
multiplication of coefficient number `n` by `n`. -/
theorem coeff_X_mul_derivative (f : PowerSeries R) (n : ℕ) :
    coeff n (X * derivative f) = (n : R) * coeff n f := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ n =>
    rw [show X * derivative f = X ^ 1 * derivative f by rw [pow_one],
      coeff_X_pow_mul, coeff_derivative]
    push_cast
    ring

/-- A formal negative-power differential equation annihilates the
coefficient vector of its solution under the weighted derivative kernel.
The conclusion includes the final coefficient, so no subtraction or division
is needed. -/
theorem sum_coeff_eq_zero_of_negPower_ode
    (κ : R) (H q : PowerSeries R)
    (hode : H * derivative q + C κ * derivative H * q = 0)
    (n : ℕ) :
    ∑ j ∈ Finset.range (n + 2),
      ((j : R) + κ * (n + 1 - j : ℕ)) * coeff (n + 1 - j) H * coeff j q = 0 := by
  have heuler :
      (X * derivative q) * H + C κ * ((X * derivative H) * q) = 0 := by
    calc
      _ = X * (H * derivative q + C κ * derivative H * q) := by ring
      _ = 0 := by rw [hode, mul_zero]
  have hc := congrArg (coeff (n + 1)) heuler
  have hqcoeff : coeff (n + 1) ((X * derivative q) * H) =
      ∑ j ∈ Finset.range (n + 2),
        (j : R) * coeff j q * coeff (n + 1 - j) H := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_X_mul_derivative]
  have hHcoeff : coeff (n + 1) ((X * derivative H) * q) =
      ∑ j ∈ Finset.range (n + 2),
        coeff j q * ((n + 1 - j : ℕ) : R) * coeff (n + 1 - j) H := by
    rw [mul_comm (X * derivative H) q, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_X_mul_derivative]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [map_add, coeff_C_mul, map_zero] at hc
  rw [hqcoeff, hHcoeff] at hc
  calc
    _ = (∑ j ∈ Finset.range (n + 2),
          (j : R) * coeff j q * coeff (n + 1 - j) H) +
        κ * ∑ j ∈ Finset.range (n + 2),
          coeff j q * ((n + 1 - j : ℕ) : R) * coeff (n + 1 - j) H := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := hc

/-- The normalized formal negative-power equation yields the usual finite
coefficient recurrence. This works over every commutative coefficient ring. -/
theorem coeff_recurrence_of_negPower_ode
    (κ : R) (H q : PowerSeries R) (hH : coeff 0 H = 1)
    (hode : H * derivative q + C κ * derivative H * q = 0)
    (n : ℕ) :
    (n + 1 : R) * coeff (n + 1) q =
      -∑ j ∈ Finset.range (n + 1),
        ((j : R) + κ * (n + 1 - j : ℕ)) *
          coeff (n + 1 - j) H * coeff j q := by
  have hsum := sum_coeff_eq_zero_of_negPower_ode κ H q hode n
  rw [show n + 2 = (n + 1) + 1 by lia, Finset.sum_range_succ] at hsum
  simp only [Nat.sub_self, Nat.cast_zero, mul_zero, add_zero, hH, mul_one,
    Nat.cast_add, Nat.cast_one] at hsum
  exact eq_neg_of_add_eq_zero_right hsum

end PowerSeries
