module

import RealRooted.DerivativeRecurrence.QuadraticInterlacing
import RealRooted.SignEvaluation
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Shifted quadratic-coefficient derivative recurrences

Nonnegative-coefficient and interlacing results for the normalized shifted recurrence.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

lemma quadratic_derivative_shift_coeff_zero_succ
    (P : ℕ → ℝ[X]) (s : ℝ)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (n : ℕ) :
    Polynomial.coeff (P (n + 1)) 0 = Polynomial.coeff (P n) 0 := by
  simpa using quadratic_derivative_linear_coeff_zero_succ P 1 1 1 s 1
    (by simpa using hrec) n

lemma hasNonnegCoeffs_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) :
    ∀ n : ℕ, HasNonnegCoeffs (P n) := by
  simpa using hasNonnegCoeffs_of_quadratic_derivative_linear P 1 1 1 s 1 h0
    (by simpa using hrec) (by positivity) (by positivity) (by positivity) hs le_rfl

lemma hasPosLeadingCoeff_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) (n : ℕ) :
    HasPosLeadingCoeff (P n) := by
  simpa using hasPosLeadingCoeff_of_quadratic_derivative_linear P 1 1 1 s 1 h0
    (by simpa using hrec) hs le_rfl n

lemma quadratic_derivative_shift_v_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (C (1) * X + C (-1) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  simpa using eval_C_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg_of_nonneg_of_nonpos
    (a := (1 : ℝ)) (b := (1 : ℝ)) (by positivity) (by positivity) hr

lemma strictInterl_step_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) (m : ℕ) (hm : 2 ≤ m) (hsp : (P m).Splits) :
    StrictInterl (P m) (P (m + 1)) := by
  simpa using strictInterl_step_of_quadratic_derivative_linear P 1 1 1 s 1 h0
    (by simpa using hrec) (by positivity) (by positivity) (by positivity) hs le_rfl m hm hsp

theorem strictInterl_of_quadratic_derivative_shift
    (P : ℕ → ℝ[X]) (s : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (P n).derivative +
        (C 1 + C (s + (n : ℝ)) * X) * P n)
    (hs : 0 < s) :
    ∀ n : ℕ, StrictInterl (P n) (P (n + 1)) := by
  simpa using strictInterl_of_quadratic_derivative_linear P 1 1 1 s 1 h0
    (by simpa using hrec) (by positivity) (by positivity) (by positivity) hs le_rfl

end RealRooted
