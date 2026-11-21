/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.FormalSine
public import RealRooted.CombinatorialExamples.CaoFu.PrincipalCoefficients
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence
import Mathlib.Tactic

/-!
# Formal coefficients of the cosecant principal part

We identify the recurrence coefficients of Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2, with the coefficients of `(X / sin X)^(2r)`.
The proof uses formal differentiation, so the identification holds in every
rank without an analytic interchange of infinite sums.
-/

public section
noncomputable section
open PowerSeries RealRooted.CenteredEulerian
namespace RealRooted.CaoFu

private theorem inverseSineQuotient_pow_mul_sinS_sq (k : ℕ) :
    inverseSineQuotient ^ (k + 2) * sinS ^ 2 = X ^ 2 * inverseSineQuotient ^ k := by
  calc
    _ = inverseSineQuotient ^ k * (sinS * inverseSineQuotient) ^ 2 := by
      rw [pow_add]; ring
    _ = _ := by rw [sinS_mul_inverseSineQuotient]; ring

/-- A formal differential recurrence for the numerator of the cosecant power. -/
theorem inverseSineQuotient_pow_add_two (k : ℕ) :
    C ((k : ℝ) * (k + 1)) * inverseSineQuotient ^ (k + 2) =
      X ^ 2 * derivative (derivative (inverseSineQuotient ^ k)) -
        C (2 * (k : ℝ)) * X * derivative (inverseSineQuotient ^ k) +
        C ((k : ℝ) * (k + 1)) * inverseSineQuotient ^ k +
        C ((k : ℝ) ^ 2) * X ^ 2 * inverseSineQuotient ^ k := by
  have hfirst := X_mul_derivative_inverseSineQuotient_pow k
  have hnext := X_mul_derivative_inverseSineQuotient_pow (k + 1)
  have hd := congrArg derivative hfirst
  simp only [derivative.leibniz, derivative_X, map_sub, derivative_C, derivative_cosS,
    smul_eq_mul, mul_zero, mul_one] at hd
  have hsquare := inverseSineQuotient_pow_mul_sinS_sq k
  have hsine : X * inverseSineQuotient ^ (k + 1) * sinS =
      X ^ 2 * inverseSineQuotient ^ k := by
    calc
      _ = X * (sinS * inverseSineQuotient) * inverseSineQuotient ^ k := by
        rw [pow_succ]; ring
      _ = _ := by rw [sinS_mul_inverseSineQuotient]; ring
  have htrig := sinS_sq_add_cosS_sq
  simp only [map_mul, map_add, map_pow, map_natCast, map_one, map_ofNat] at hd hfirst hnext ⊢
  push_cast at hnext
  linear_combination -X * hd + (k : ℝ⟦X⟧) * cosS * hnext +
    (k + 1 : ℝ⟦X⟧) * hfirst +
    -(k : ℝ⟦X⟧) * (k + 1) * inverseSineQuotient ^ (k + 2) * htrig +
    (k : ℝ⟦X⟧) * (k + 1) * hsquare - (k : ℝ⟦X⟧) * hsine

private theorem coeff_X_sq_mul_derivative_two (F : ℝ⟦X⟧) (m : ℕ) :
    coeff m (X ^ 2 * derivative (derivative F)) =
      (m : ℝ) * (m - 1) * coeff m F := by
  cases m with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp [coeff_X_pow_mul']
    | succ m =>
      rw [coeff_X_pow_mul', ite_eq_left (by lia),
        show m + 1 + 1 - 2 = m by lia, coeff_derivative, coeff_derivative]
      push_cast
      ring

/-- The coefficient recurrence for the even powers of `X / sin X`. -/
theorem coeff_inverseSineQuotient_pow_add_two (k m : ℕ) :
    ((k : ℝ) * (k + 1)) * coeff m (inverseSineQuotient ^ (k + 2)) =
      ((m : ℝ) * (m - 1) - 2 * k * m + k * (k + 1)) *
        coeff m (inverseSineQuotient ^ k) +
      (k : ℝ) ^ 2 * (if 2 ≤ m then coeff (m - 2) (inverseSineQuotient ^ k) else 0) := by
  have h := congrArg (coeff m) (inverseSineQuotient_pow_add_two k)
  simp only [map_add, map_sub, mul_assoc, coeff_C_mul] at h
  rw [coeff_X_sq_mul_derivative_two, PowerSeries.coeff_X_mul_derivative,
    coeff_X_pow_mul'] at h
  linear_combination h

/-- The principal-part coefficients are the low coefficients of `(X / sin X)^(2r)`. -/
theorem principalCoeff_eq_coeff_inverseSineQuotient_pow (n j : ℕ) (hj : j ≤ n) :
    principalCoeff n j =
      coeff (2 * (n - j)) (inverseSineQuotient ^ (2 * (n + 1))) := by
  induction n generalizing j with
  | zero =>
    have hj0 : j = 0 := by lia
    subst j
    simp [principalCoeff, coeff_zero_eq_constantCoeff_apply]
  | succ n ih =>
    by_cases hjtop : j = n + 1
    · subst j
      simp [coeff_zero_eq_constantCoeff_apply]
    have hjn : j ≤ n := by lia
    have h := coeff_inverseSineQuotient_pow_add_two (2 * (n + 1)) (2 * (n + 1 - j))
    have hm : 2 * (n + 1 - j) - 2 = 2 * (n - j) := by lia
    have hge : 2 ≤ 2 * (n + 1 - j) := by lia
    rw [ite_eq_left hge, hm, ← ih j hjn] at h
    have hidx : 2 * (n + 1) + 2 = 2 * (n + 1 + 1) := by lia
    rw [hidx] at h
    have hfactor :
        ((2 * (n + 1 - j) : ℕ) : ℝ) * (((2 * (n + 1 - j) : ℕ) : ℝ) - 1) -
          2 * ((2 * (n + 1) : ℕ) : ℝ) * ((2 * (n + 1 - j) : ℕ) : ℝ) +
          ((2 * (n + 1) : ℕ) : ℝ) * (((2 * (n + 1) : ℕ) : ℝ) + 1) =
          2 * (j : ℝ) * (2 * j + 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by lia)]
      push_cast
      ring
    rw [hfactor] at h
    have hfirst : (2 * (j : ℝ) * (2 * j + 1)) *
        coeff (2 * (n + 1 - j)) (inverseSineQuotient ^ (2 * (n + 1))) =
        (2 * (j : ℝ) * (2 * j + 1)) * principalCoeff n (j - 1) := by
      by_cases hj0 : j = 0
      · simp [hj0]
      · have hjprev : j - 1 ≤ n := by lia
        rw [ih (j - 1) hjprev, show n - (j - 1) = n + 1 - j by lia]
    rw [hfirst] at h
    rw [principalCoeff]
    apply (div_eq_iff (by positivity :
      (2 * (n + 1 : ℝ) * (2 * (n + 1) + 1)) ≠ 0)).mpr
    push_cast at h
    linear_combination -h

/-- The principal coefficient is the coefficient after the arcsine change of variable. -/
theorem coeff_X_pow_mul_tangent_subst_arcsin_eq_principalCoeff (n j : ℕ) (hj : j ≤ n) :
    coeff (2 * (n + 1)) ((X ^ (2 * j + 1) * sinS * secS).subst fS) =
      principalCoeff n j := by
  rw [coeff_X_pow_mul_tangent_subst_arcsin (n + 1) j (by lia),
    principalCoeff_eq_coeff_inverseSineQuotient_pow n j hj,
    show n + 1 - (j + 1) = n - j by lia]

end RealRooted.CaoFu
