module

import RealRooted.DerivativeRecurrence.QuadraticDegree
import RealRooted.DerivativeRecurrence.Interlacing
public import RealRooted.MaWang
import RealRooted.SignEvaluation
import RealRooted.Linear
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Interlacing for quadratic-coefficient derivative recurrences

Nonnegative-coefficient and interlacing results for the general
linear-multiplier recurrence, a special case of the first-order derivative recurrence
theorems of `RealRooted.DerivativeRecurrence.Interlacing`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

theorem hasNonnegCoeffs_of_quadratic_derivative_bilinear
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hs : 0 < s) (hbt : b ≤ t) :
    ∀ n : ℕ, HasNonnegCoeffs (P n) := by
  have hdeg := natDegree_of_quadratic_derivative_bilinear P a b c u s t h0 hrec hs hbt
  refine derivativeRecurrence_hasNonnegCoeffs_of_mult (D₀ := 0) (d := 1)
    (A := fun _ => C a * X + C (-b) * X ^ 2)
    (B := fun n => C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) hrec
    (fun n => by simpa using (hdeg n).le) (fun n => by simp) ?_
    (by rw [h0]; exact hasNonnegCoeffs_one)
  intro n i j hj
  have hj' : (j : ℝ) ≤ n := by exact_mod_cast (by simpa using hj : j ≤ n)
  have hn : (0 : ℝ) ≤ n := by positivity
  have hj0 : (0 : ℝ) ≤ j := by positivity
  rcases i with _ | _ | i <;>
    simp [coeff_X, coeff_C, coeff_X_pow] <;>
    nlinarith [mul_nonneg ha hj0, mul_nonneg hu hn, mul_nonneg (sub_nonneg.mpr hbt) hn,
      mul_nonneg hb (sub_nonneg.mpr hj')]

theorem strictInterl_of_quadratic_derivative_bilinear
    (P : ℕ → ℝ[X]) (a b c u s t : ℝ)
    (h0 : P 0 = 1)
    (hrec : ∀ n, P (n + 1) =
      (C a * X + C (-b) * X ^ 2) * (P n).derivative +
        (C (c + u * (n : ℝ)) + C (s + t * (n : ℝ)) * X) * P n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hs : 0 < s) (hbt : b ≤ t) :
    ∀ n : ℕ, StrictInterl (P n) (P (n + 1)) := by
  have hdeg := natDegree_of_quadratic_derivative_bilinear P a b c u s t h0 hrec hs hbt
  have hpos := leadingCoeff_pos_of_quadratic_derivative_bilinear P a b c u s t h0 hrec hs hbt
  have hnn := hasNonnegCoeffs_of_quadratic_derivative_bilinear P a b c u s t h0 hrec
    ha hb hc hu hs hbt
  intro n
  induction n with
  | zero =>
      rw [h0]
      exact (interlaces_one_linear (p := P 1) (by rw [hdeg])).toStrictInterl
  | succ n ih =>
      refine derivativeRecurrence_strictInterl_step (hrec (n + 1)) ih.2.1.2
        (by rw [hdeg]; lia) (hpos (n + 1)) (hpos (n + 2)) (by rw [hdeg, hdeg]; lia)
        (by rw [hdeg, hdeg]) fun r hr => ?_
      have hne : P (n + 1) ≠ 0 := leadingCoeff_ne_zero.mp (hpos (n + 1)).ne'
      exact eval_C_mul_X_add_C_neg_mul_X_sq_nonpos_of_nonneg_of_nonneg_of_nonpos ha hb
        (roots_nonpos_of_hasNonnegCoeffs (hnn (n + 1)) r ((mem_roots hne).mpr hr))

end RealRooted
