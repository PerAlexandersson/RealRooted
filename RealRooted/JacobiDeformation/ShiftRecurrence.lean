import RealRooted.JacobiDeformation.Basic
import RealRooted.EulerOperator

/-!
# Unit parameter shift for the Jacobi deformation

This module proves the exact operator recurrence (25), first in a denominator-
free form and then in its quotient form when the scalar denominator is nonzero.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

theorem mul_risingFactorial_add_one (a : ℝ) (n : ℕ) :
    a * risingFactorial (a + 1) n =
      (a + n) * risingFactorial a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [risingFactorial_succ, risingFactorial_succ]
      push_cast
      linear_combination (a + (n : ℝ) + 1) * ih

theorem summand_shift (m i j : ℕ) (δ c d U V : ℝ) :
    ((m : ℝ) + c + d - 1 + δ) * summand m (δ + 1) c d U V i j =
      ((m : ℝ) + c + d - 1 + δ + (i + j : ℕ)) *
        summand m δ c d U V i j := by
  let b : ℝ := (m : ℝ) + c + d - 1 + δ
  let K : ℝ :=
    (m.factorial : ℝ) /
        (((m - i - j).factorial : ℝ) * i.factorial * j.factorial) /
      (risingFactorial c i * risingFactorial d j) * U ^ i * V ^ j
  have hform (ε : ℝ) : summand m ε c d U V i j =
      K * risingFactorial ((m : ℝ) + c + d - 1 + ε) (i + j) := by
    unfold summand
    dsimp [K]
    ring
  rw [hform, hform]
  have hshift := mul_risingFactorial_add_one b (i + j)
  dsimp [b] at hshift ⊢
  rw [show (m : ℝ) + c + d - 1 + (δ + 1) =
      ((m : ℝ) + c + d - 1 + δ) + 1 by ring]
  linear_combination K * hshift

theorem coeff_polynomial_shift (m k : ℕ) (δ c d U V : ℝ) :
    ((m : ℝ) + c + d - 1 + δ) *
        (polynomial m (δ + 1) c d U V).coeff k =
      ((m : ℝ) + c + d - 1 + δ + (m - k : ℕ)) *
        (polynomial m δ c d U V).coeff k := by
  by_cases hk : k ≤ m
  · rw [coeff_polynomial, coeff_polynomial, ite_eq_left hk, ite_eq_left hk,
      Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    have hijsum : ij.1 + ij.2 = m - k := by
      exact HasAntidiagonal.mem_antidiagonal.mp hij
    simpa [hijsum] using summand_shift m ij.1 ij.2 δ c d U V
  · rw [coeff_polynomial, coeff_polynomial, ite_eq_right hk, ite_eq_right hk]
    ring

/-- Equation (25) without division by its scalar denominator. -/
theorem polynomial_shift_cleared (m : ℕ) (δ c d U V : ℝ) :
    C ((m : ℝ) + c + d - 1 + δ) * polynomial m (δ + 1) c d U V =
      C ((m : ℝ) + c + d - 1 + δ + m) * polynomial m δ c d U V -
        X * (polynomial m δ c d U V).derivative := by
  rw [show X * (polynomial m δ c d U V).derivative =
      theta (polynomial m δ c d U V) by rfl]
  ext k
  rw [coeff_C_mul, coeff_sub, coeff_C_mul, coeff_theta]
  have hcoeff := coeff_polynomial_shift m k δ c d U V
  by_cases hk : k ≤ m
  · have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by
      rw [Nat.cast_sub hk]
    rw [hcast] at hcoeff
    linarith
  · have hzero : (polynomial m δ c d U V).coeff k = 0 := by
      rw [coeff_polynomial, ite_eq_right hk]
    have hzero' : (polynomial m (δ + 1) c d U V).coeff k = 0 := by
      rw [coeff_polynomial, ite_eq_right hk]
    rw [hzero, hzero']
    ring

/-- Equation (25) in quotient form. -/
theorem polynomial_shift (m : ℕ) (δ c d U V : ℝ)
    (hb : (m : ℝ) + c + d - 1 + δ ≠ 0) :
    polynomial m (δ + 1) c d U V =
      C (((m : ℝ) + c + d - 1 + δ)⁻¹) *
        (C ((m : ℝ) + c + d - 1 + δ + m) *
          polynomial m δ c d U V -
            X * (polynomial m δ c d U V).derivative) := by
  rw [← polynomial_shift_cleared]
  symm
  calc
    C (((m : ℝ) + c + d - 1 + δ)⁻¹) *
          (C ((m : ℝ) + c + d - 1 + δ) * polynomial m (δ + 1) c d U V) =
        (C (((m : ℝ) + c + d - 1 + δ)⁻¹) *
          C ((m : ℝ) + c + d - 1 + δ)) * polynomial m (δ + 1) c d U V := by
      rw [mul_assoc]
    _ = C (((m : ℝ) + c + d - 1 + δ)⁻¹ *
          ((m : ℝ) + c + d - 1 + δ)) * polynomial m (δ + 1) c d U V := by
      rw [C_mul]
    _ = polynomial m (δ + 1) c d U V := by
      rw [inv_mul_cancel₀ hb]
      simp

end RealRooted.JacobiDeformation
