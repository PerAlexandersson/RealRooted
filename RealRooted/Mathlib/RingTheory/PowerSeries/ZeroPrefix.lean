import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Removing a finite zero prefix from a power series

This file provides the coefficient shift inverse to multiplication by a fixed
power of `X`.  The construction is algebraic and does not require an order,
topology, or a nonzero scalar.
-/

namespace PowerSeries

noncomputable section

variable {R : Type*}

/-- Remove the first `N` coefficients of a formal power series. -/
def dropPrefix [Semiring R] (N : ℕ) (f : R⟦X⟧) : R⟦X⟧ :=
  mk fun d => coeff (d + N) f

@[simp]
theorem coeff_dropPrefix [Semiring R] (N d : ℕ) (f : R⟦X⟧) :
    coeff d (dropPrefix N f) = coeff (d + N) f := by
  simp [dropPrefix]

@[simp]
theorem dropPrefix_zero [Semiring R] (N : ℕ) :
    dropPrefix N (0 : R⟦X⟧) = 0 := by
  ext d
  simp

@[simp]
theorem dropPrefix_zero_index [Semiring R] (f : R⟦X⟧) :
    dropPrefix 0 f = f := by
  ext d
  simp

@[simp]
theorem dropPrefix_X_pow_mul [Semiring R] (N : ℕ) (f : R⟦X⟧) :
    dropPrefix N (X ^ N * f) = f := by
  ext d
  simp [coeff_X_pow_mul']

@[simp]
theorem dropPrefix_C_mul_X_pow_mul [Semiring R]
    (c : R) (N : ℕ) (f : R⟦X⟧) :
    dropPrefix N (C c * X ^ N * f) = C c * f := by
  ext d
  rw [coeff_dropPrefix, coeff_C_mul]
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp

theorem C_inv_mul_dropPrefix_C_mul_X_pow_mul
    {K : Type*} [Field K] {c : K} (hc : c ≠ 0)
    (N : ℕ) (f : K⟦X⟧) :
    C c⁻¹ * dropPrefix N (C c * X ^ N * f) = f := by
  rw [dropPrefix_C_mul_X_pow_mul]
  rw [← mul_assoc, ← map_mul]
  simp [hc]

end

end PowerSeries
