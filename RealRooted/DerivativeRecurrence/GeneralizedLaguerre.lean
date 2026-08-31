import RealRooted.Basic

/-!
# Generalized-Laguerre differential recurrences

The differential recurrence of a generalized-Laguerre family has a first-order
form. This module records the algebraic reduction independently of any chosen
initial polynomial or real-rootedness argument.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The generalized-Laguerre differential invariant. -/
theorem generalized_laguerre_second_derivative_ode
    {P : ℕ → ℝ[X]} {m c : ℝ} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative) :
    ∀ n, C m * X * (P n).derivative.derivative +
      (C c + X) * (P n).derivative = C (n : ℝ) * P n
  | 0 => by simp [hzero]
  | n + 1 => by
      have ih := generalized_laguerre_second_derivative_ode hzero hrec n
      have hred : P (n + 1) =
          (C m * C (n : ℝ) + C c + X) * P n + C m * X * (P n).derivative := by
        rw [hrec n]
        calc
          (C c + X) * P n +
              (C (m * c) + C (2 * m) * X) * (P n).derivative +
                C (m ^ 2) * X * (P n).derivative.derivative =
              (C c + X) * P n +
                C m * (C m * X * (P n).derivative.derivative +
                  (C c + X) * (P n).derivative) +
                    C m * X * (P n).derivative := by
              norm_num [map_add, map_mul, map_pow, map_ofNat]
              ring
          _ = (C m * C (n : ℝ) + C c + X) * P n +
                C m * X * (P n).derivative := by
              rw [ih]
              ring
      have ihd := congrArg Polynomial.derivative ih
      simp only [derivative_add, derivative_mul, derivative_X, derivative_C,
        zero_mul, zero_add, one_mul] at ihd
      rw [hred]
      simp only [derivative_add, derivative_mul, derivative_X, derivative_C,
        derivative_zero, derivative_one, zero_mul]
      push_cast
      simp only [map_add, map_one]
      linear_combination
        (C m * X) * ihd + (C m * C (n : ℝ) + C c + X + C m) * ih

/-- The first-order recurrence induced by the generalized-Laguerre invariant. -/
theorem generalized_laguerre_second_derivative_reduced
    {P : ℕ → ℝ[X]} {m c : ℝ} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative) (n : ℕ) :
    P (n + 1) =
      (C (m * (n : ℝ) + c) + X) * P n + C m * X * (P n).derivative := by
  rw [hrec n]
  calc
    (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative =
        (C c + X) * P n +
          C m * (C m * X * (P n).derivative.derivative +
            (C c + X) * (P n).derivative) + C m * X * (P n).derivative := by
      norm_num [map_add, map_mul, map_pow, map_ofNat]
      ring
    _ = (C m * C (n : ℝ) + C c + X) * P n + C m * X * (P n).derivative := by
      rw [generalized_laguerre_second_derivative_ode hzero hrec n]
      ring
    _ = (C (m * (n : ℝ) + c) + X) * P n + C m * X * (P n).derivative := by
      simp only [map_add, map_mul]

end RealRooted
