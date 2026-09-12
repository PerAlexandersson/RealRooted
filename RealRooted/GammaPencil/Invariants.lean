/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.GammaPencil.Basic
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Coefficient and degree invariants of the gamma pencil

The coefficient form of the gamma operator is triangular.  Its two terms have
nonnegative multipliers throughout the degree box occupied by the pencil;
outside that box both input coefficients vanish (with the even-rank boundary
canceling exactly).
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ### The coefficient recurrence -/

/-- Coefficients of one gamma-operator step. -/
theorem gammaOperator_coeff (n k : ℕ) (p : ℝ[X]) :
    (gammaOperator n p).coeff (k + 1) =
      ((k : ℝ) + 2) * p.coeff (k + 1) +
        (2 * (n : ℝ) - 4 * (k : ℝ)) * p.coeff k := by
  rw [gammaOperator_apply]
  rw [show
      (1 + C (2 * (n : ℝ)) * X) * p +
          X * (1 - C (4 : ℝ) * X) * p.derivative =
        (C (1 : ℝ) * X + C (-4 : ℝ) * X ^ 2) * p.derivative +
          (C (1 : ℝ) + C (2 * (n : ℝ)) * X) * p by
        simp only [map_neg, map_one]
        ring]
  rw [coeff_quadratic_derivative_add_linear_mul_succ]
  ring

/-! ### One-step positivity and degree control -/

private theorem gammaOperator_hasNonnegCoeffs_of_natDegree_le
    {p : ℝ[X]} (hn : p.natDegree ≤ n / 2) (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (gammaOperator n p) := by
  intro j
  cases j with
  | zero =>
      simpa [gammaOperator_constantCoeff] using hp 0
  | succ k =>
      rw [gammaOperator_coeff]
      by_cases hk : k ≤ n / 2
      · have hkn : 2 * k ≤ n := by lia
        have hkn' : (2 : ℝ) * (k : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hkn
        exact add_nonneg
          (mul_nonneg (by positivity) (hp (k + 1)))
          (mul_nonneg (by nlinarith) (hp k))
      · have hkdeg : p.natDegree < k := by lia
        have hkdeg' : p.natDegree < k + 1 := by lia
        rw [coeff_eq_zero_of_natDegree_lt hkdeg',
          coeff_eq_zero_of_natDegree_lt hkdeg]
        simp

private theorem gammaOperator_natDegree_le_of_natDegree_le
    {p : ℝ[X]} (hn : p.natDegree ≤ n / 2) :
    (gammaOperator n p).natDegree ≤ (n + 1) / 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  cases j with
  | zero => simp at hj
  | succ k =>
      rw [gammaOperator_coeff]
      have hkone : p.natDegree < k + 1 := by
        have hdiv : n / 2 ≤ (n + 1) / 2 := by lia
        lia
      rw [coeff_eq_zero_of_natDegree_lt hkone]
      by_cases hk : p.natDegree < k
      · rw [coeff_eq_zero_of_natDegree_lt hk]
        simp
      · have hkle : k ≤ p.natDegree := Nat.le_of_not_gt hk
        have hkn : k ≤ n / 2 := hkle.trans hn
        have hboundary : n = 2 * k := by lia
        rw [hboundary]
        push_cast
        ring

/-! ### The two gamma components -/

theorem gammaU_natDegree_le_add_two (n : ℕ) :
    (gammaU (n + 2)).natDegree ≤ (n + 2) / 2 := by
  induction n with
  | zero => simp [gammaU]
  | succ n ih =>
      change (gammaOperator (n + 2) (gammaU (n + 2))).natDegree ≤ (n + 3) / 2
      exact gammaOperator_natDegree_le_of_natDegree_le ih

theorem gammaV_natDegree_le_add_two (n : ℕ) :
    (gammaV (n + 2)).natDegree ≤ (n + 2) / 2 := by
  induction n with
  | zero => simp [gammaV]
  | succ n ih =>
      change (gammaOperator (n + 2) (gammaV (n + 2))).natDegree ≤ (n + 3) / 2
      exact gammaOperator_natDegree_le_of_natDegree_le ih

theorem gammaU_hasNonnegCoeffs_add_two (n : ℕ) :
    HasNonnegCoeffs (gammaU (n + 2)) := by
  induction n with
  | zero => exact hasNonnegCoeffs_one
  | succ n ih =>
      change HasNonnegCoeffs (gammaOperator (n + 2) (gammaU (n + 2)))
      exact gammaOperator_hasNonnegCoeffs_of_natDegree_le
        (gammaU_natDegree_le_add_two n) ih

theorem gammaV_hasNonnegCoeffs_add_two (n : ℕ) :
    HasNonnegCoeffs (gammaV (n + 2)) := by
  induction n with
  | zero => simpa using hasNonnegCoeffs_X
  | succ n ih =>
      change HasNonnegCoeffs (gammaOperator (n + 2) (gammaV (n + 2)))
      exact gammaOperator_hasNonnegCoeffs_of_natDegree_le
        (gammaV_natDegree_le_add_two n) ih

theorem gammaU_ne_zero_add_two (n : ℕ) : gammaU (n + 2) ≠ 0 := by
  intro hzero
  have hconstant := congrArg constantCoeff hzero
  rw [gammaU_constantCoeff_add_two] at hconstant
  simp at hconstant

theorem gammaU_hasNonnegCoeffs (n : ℕ) (hn : 2 ≤ n) :
    HasNonnegCoeffs (gammaU n) := by
  rw [← Nat.sub_add_cancel hn]
  exact gammaU_hasNonnegCoeffs_add_two (n - 2)

theorem gammaU_natDegree_le (n : ℕ) (hn : 2 ≤ n) :
    (gammaU n).natDegree ≤ n / 2 := by
  rw [← Nat.sub_add_cancel hn]
  simpa using gammaU_natDegree_le_add_two (n - 2)

theorem gammaU_ne_zero (n : ℕ) (hn : 2 ≤ n) : gammaU n ≠ 0 := by
  rw [← Nat.sub_add_cancel hn]
  exact gammaU_ne_zero_add_two (n - 2)

/-! ### The distinguished coefficient of the parameter component -/

theorem gammaV_coeff_one_add_two (n : ℕ) :
    (gammaV (n + 2)).coeff 1 = 2 ^ n := by
  induction n with
  | zero => simp [gammaV]
  | succ n ih =>
      calc
        (gammaV (n + 1 + 2)).coeff 1 =
            2 * (gammaV (n + 2)).coeff 1 := by
              change (gammaOperator (n + 2) (gammaV (n + 2))).coeff 1 = _
              rw [gammaOperator_coeff]
              rw [show (gammaV (n + 2)).coeff 0 = 0 from
                gammaV_constantCoeff_add_two n]
              ring
        _ = 2 ^ (n + 1) := by rw [ih, pow_succ]; ring

theorem gammaV_coeff_one (n : ℕ) (hn : 2 ≤ n) :
    (gammaV n).coeff 1 = 2 ^ (n - 2) := by
  rw [← Nat.sub_add_cancel hn]
  simpa using gammaV_coeff_one_add_two (n - 2)

theorem gammaV_ne_zero_add_two (n : ℕ) : gammaV (n + 2) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) hzero
  rw [gammaV_coeff_one_add_two] at hcoeff
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [coeff_zero] at hcoeff
  exact (ne_of_gt hpow) hcoeff

theorem gammaV_hasNonnegCoeffs (n : ℕ) (hn : 2 ≤ n) :
    HasNonnegCoeffs (gammaV n) := by
  rw [← Nat.sub_add_cancel hn]
  exact gammaV_hasNonnegCoeffs_add_two (n - 2)

theorem gammaV_natDegree_le (n : ℕ) (hn : 2 ≤ n) :
    (gammaV n).natDegree ≤ n / 2 := by
  rw [← Nat.sub_add_cancel hn]
  simpa using gammaV_natDegree_le_add_two (n - 2)

theorem gammaV_ne_zero (n : ℕ) (hn : 2 ≤ n) : gammaV n ≠ 0 := by
  rw [← Nat.sub_add_cancel hn]
  exact gammaV_ne_zero_add_two (n - 2)

/-! ### The affine pencil -/

theorem gammaPencil_hasNonnegCoeffs_add_two {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    HasNonnegCoeffs (gammaPencil a (n + 2)) := by
  rw [gammaPencil, Polynomial.smul_eq_C_mul]
  exact (gammaU_hasNonnegCoeffs_add_two n).add
    (nonnegCoeffs_C_mul ha (gammaV_hasNonnegCoeffs_add_two n))

theorem gammaPencil_natDegree_le_add_two (a : ℝ) (n : ℕ) :
    (gammaPencil a (n + 2)).natDegree ≤ (n + 2) / 2 := by
  rw [gammaPencil, Polynomial.smul_eq_C_mul]
  exact (natDegree_add_le _ _).trans <| max_le
    (gammaU_natDegree_le_add_two n)
    ((natDegree_C_mul_le _ _).trans (gammaV_natDegree_le_add_two n))

theorem gammaPencil_constantCoeff_add_two_ne_zero (a : ℝ) (n : ℕ) :
    gammaPencil a (n + 2) ≠ 0 := by
  intro hzero
  have hconstant := congrArg constantCoeff hzero
  rw [gammaPencil_constantCoeff_add_two] at hconstant
  simp at hconstant

theorem gammaPencil_hasNonnegCoeffs {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hn : 2 ≤ n) :
    HasNonnegCoeffs (gammaPencil a n) := by
  rw [← Nat.sub_add_cancel hn]
  exact gammaPencil_hasNonnegCoeffs_add_two ha (n - 2)

theorem gammaPencil_natDegree_le (a : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (gammaPencil a n).natDegree ≤ n / 2 := by
  rw [← Nat.sub_add_cancel hn]
  simpa using gammaPencil_natDegree_le_add_two a (n - 2)

theorem gammaPencil_ne_zero (a : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    gammaPencil a n ≠ 0 := by
  rw [← Nat.sub_add_cancel hn]
  exact gammaPencil_constantCoeff_add_two_ne_zero a (n - 2)

end RealRooted
