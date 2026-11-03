module

import RealRooted.DerivativeRecurrence.Degree
import Mathlib.Tactic.ComputeDegree
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic

/-!
# Degree of quadratic-coefficient derivative recurrences

Degree and leading-coefficient results for the derivative recurrences `P 0 = 1`,
`P (n + 1) = (a X - b X ^ 2) P n' + ((c + u n) + (s + t n) X) P n`, a special case of
`derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos`.  The real-root and interlacing
consequences live in `QuadraticInterlacing`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private theorem natDegree_eq_and_leadingCoeff_pos_of_quadratic_derivative_bilinear
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n ∧ 0 < (P n).leadingCoeff := by
  simpa using derivativeRecurrence_natDegree_eq_and_leadingCoeff_pos (P := P) (d := 1) (D₀ := 0)
    (A := fun _ => C a * X + C (-b) * X ^ 2)
    (B := fun n => C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) hrec
    (fun _ => by compute_degree!) (fun _ => by compute_degree!) (by simp [h0]) (by simp [h0])
    (by simp [h0]) (fun n => by
      simp [coeff_C, coeff_X_pow]
      nlinarith [mul_nonneg (sub_nonneg.mpr hbt) (Nat.cast_nonneg (α := ℝ) n)]) n

theorem natDegree_of_quadratic_derivative_bilinear
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    (P n).natDegree = n :=
  (natDegree_eq_and_leadingCoeff_pos_of_quadratic_derivative_bilinear
    P a b c u s t h0 hrec hs hbt n).1

theorem leadingCoeff_pos_of_quadratic_derivative_bilinear
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (hs : 0 < s) (hbt : b ≤ t) (n : ℕ) :
    0 < (P n).leadingCoeff :=
  (natDegree_eq_and_leadingCoeff_pos_of_quadratic_derivative_bilinear
    P a b c u s t h0 hrec hs hbt n).2

end RealRooted
