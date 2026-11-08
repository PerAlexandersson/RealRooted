module

import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Hessenberg
public import RealRooted.BrandenLeite.WeightedDerivativeKernel.Basic
import Mathlib.Tactic

/-! Weighted kernel determinants from formal coefficient recurrences. -/

public section

open Matrix

namespace RealRooted.BrandenLeite

variable {R : Type*} [CommRing R]

/-- The coefficient recurrence of a formal negative power annihilates its
coefficient vector under the weighted differential kernel. -/
theorem weightedDerivativeKernel_sum_eq_zero_of_recurrence
    (κ : R) (h q : ℕ → R) (hzero : h 0 = 1)
    (hq : ∀ n : ℕ, (n + 1 : R) * q (n + 1) =
      -∑ j ∈ Finset.range (n + 1),
        ((j : R) + κ * (n + 1 - j : ℕ)) * h (n + 1 - j) * q j)
    (i : ℕ) :
    ∑ j ∈ Finset.range (i + 2), weightedDerivativeKernel κ h i j * q j = 0 := by
  have hs :
      (∑ j ∈ Finset.range (i + 2), weightedDerivativeKernel κ h i j * q j) =
        ∑ j ∈ Finset.range (i + 2),
          ((j : R) + κ * (i + 1 - j : ℕ)) * h (i + 1 - j) * q j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ i + 1 := by have := Finset.mem_range.mp hj; lia
    simp [weightedDerivativeKernel, hj']
  rw [hs, show i + 2 = (i + 1) + 1 by lia, Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.cast_zero, mul_zero, add_zero, hzero, mul_one]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hq]
  exact add_neg_cancel _

/-- Multiplying coefficient number `k` by `(-1)^k` corresponds to changing
the formal variable's sign. The same sign change preserves annihilation of
the coefficient vector. -/
theorem weightedDerivativeKernel_signed_sum_eq_zero
    (κ : R) (h q : ℕ → R)
    (hq : ∀ i, ∑ j ∈ Finset.range (i + 2),
      weightedDerivativeKernel κ h i j * q j = 0) (i : ℕ) :
    ∑ j ∈ Finset.range (i + 2),
      weightedDerivativeKernel κ (fun k => (-1 : R) ^ k * h k) i j *
        ((-1 : R) ^ j * q j) = 0 := by
  calc
    _ = (-1 : R) ^ (i + 1) *
        ∑ j ∈ Finset.range (i + 2), weightedDerivativeKernel κ h i j * q j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ i + 1 := by have := Finset.mem_range.mp hj; lia
      have hsign : (-1 : R) ^ (i + 1 - j) * (-1 : R) ^ j =
          (-1 : R) ^ (i + 1) := by
        rw [← pow_add, Nat.sub_add_cancel hj']
      simp only [weightedDerivativeKernel, ite_eq_left hj']
      calc
        _ = ((-1 : R) ^ (i + 1 - j) * (-1 : R) ^ j) *
            (((j : R) + κ * (i + 1 - j : ℕ)) * h (i + 1 - j) * q j) := by
          ring
        _ = _ := by rw [hsign]
    _ = 0 := by rw [hq, mul_zero]

/-- The factorial-scaled coefficients of a normalized formal negative
power are determinants of the weighted kernel with sign-reversed input.
This identity is valid over every commutative ring; no division or
invertibility is used. -/
theorem det_weightedDerivativeKernel_signed_of_recurrence
    (κ : R) (h q : ℕ → R) (hzero : h 0 = 1) (qzero : q 0 = 1)
    (hq : ∀ n : ℕ, (n + 1 : R) * q (n + 1) =
      -∑ j ∈ Finset.range (n + 1),
        ((j : R) + κ * (n + 1 - j : ℕ)) * h (n + 1 - j) * q j)
    (n : ℕ) :
    ((weightedDerivativeKernel κ (fun k => (-1 : R) ^ k * h k)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) R).det =
        (n.factorial : R) * q n := by
  have hrow := weightedDerivativeKernel_sum_eq_zero_of_recurrence κ h q hzero hq
  have hdet := det_leading_eq_factorial_mul_of_sum_eq_zero
    (weightedDerivativeKernel κ (fun k => (-1 : R) ^ k * h k))
    (fun k => (-1 : R) ^ k * q k)
    (fun i j hij => by simp [weightedDerivativeKernel, Nat.not_le.mpr hij])
    (fun i => by simp [weightedDerivativeKernel, hzero])
    (by simp [qzero])
    (weightedDerivativeKernel_signed_sum_eq_zero κ h q hrow) n
  rw [hdet]
  calc
    _ = ((-1 : R) ^ n * (-1 : R) ^ n) * ((n.factorial : R) * q n) := by ring
    _ = _ := by rw [← mul_pow]; simp

end RealRooted.BrandenLeite
