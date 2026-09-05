import RealRooted.DerivativeRecurrence.GeneralizedLaguerre
import RealRooted.DerivativeRecurrence.QuadraticInterlacing

/-!
# Interlacing for generalized-Laguerre differential recurrences

This module applies the algebraic generalized-Laguerre reduction to the
bilinear derivative-recurrence interlacing API.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The generalized-Laguerre reduction in the bilinear recurrence form used by
the degree and interlacing API. -/
theorem generalized_laguerre_second_derivative_bilinear
    {P : ℕ → ℝ[X]} {m c : ℝ} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative) :
    ∀ n, P (n + 1) =
      (C m * X + C (-(0 : ℝ)) * X ^ 2) * (P n).derivative +
        (C (c + m * (n : ℝ)) + C (1 + 0 * (n : ℝ)) * X) * P n := by
  intro n
  rw [generalized_laguerre_second_derivative_reduced hzero hrec n]
  simp
  ring

/-- Every row of a generalized-Laguerre second-derivative sequence has degree
equal to its index. -/
theorem natDegree_of_generalized_laguerre_second_derivative
    {P : ℕ → ℝ[X]} {m c : ℝ} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative) :
    ∀ n, (P n).natDegree = n := by
  exact natDegree_of_quadratic_derivative_bilinear P m 0 c m 1 0 hzero
    (generalized_laguerre_second_derivative_bilinear hzero hrec) (by norm_num) (by norm_num)

/-- Consecutive rows of a generalized-Laguerre second-derivative sequence are
in proper position when both parameters are nonnegative. -/
theorem prec_of_generalized_laguerre_second_derivative
    {P : ℕ → ℝ[X]} {m c : ℝ} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative)
    (hm : 0 ≤ m) (hc : 0 ≤ c) :
    ∀ n, Prec (P n) (P (n + 1)) := by
  exact prec_of_quadratic_derivative_bilinear P m 0 c m 1 0 hzero
    (generalized_laguerre_second_derivative_bilinear hzero hrec)
    hm (by norm_num) hc hm (by norm_num) (by norm_num)

/-- Consecutive rows of a generalized-Laguerre second-derivative sequence
interlace when both parameters are nonnegative. -/
theorem interlaces_of_generalized_laguerre_second_derivative
    {P : ℕ → ℝ[X]} {m c : ℝ} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative)
    (hm : 0 ≤ m) (hc : 0 ≤ c) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  intro n
  exact (prec_of_generalized_laguerre_second_derivative hzero hrec hm hc n).toInterlaces (by
    rw [natDegree_of_generalized_laguerre_second_derivative hzero hrec,
      natDegree_of_generalized_laguerre_second_derivative hzero hrec])

/-- Every row of a generalized-Laguerre second-derivative sequence is nonzero
and real-rooted when both parameters are nonnegative. -/
theorem isRealRooted_of_generalized_laguerre_second_derivative_sequence
    {P : ℕ → ℝ[X]} {m c : ℝ} (hzero : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C c + X) * P n +
        (C (m * c) + C (2 * m) * X) * (P n).derivative +
          C (m ^ 2) * X * (P n).derivative.derivative)
    (hm : 0 ≤ m) (hc : 0 ≤ c) :
    ∀ n, P n ≠ 0 ∧ (P n).Splits := fun n =>
  (prec_of_generalized_laguerre_second_derivative hzero hrec hm hc n).1

end RealRooted
