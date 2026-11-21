/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Coefficients of the cosecant principal part

The recurrence in Cao--Fu, arXiv:2610.40496v1, Lemma 3.2, equation (3.6),
constructs the coefficients of the principal part of `csc^(2r)`.
We use zero-based indices: `principalCoeff n j` is the paper's `a_(n+1,j+1)`.
This file proves positivity, finite support, and the top coefficient one.
The analytic identification with the Laurent principal part is separate.
-/

@[expose] public section

noncomputable section

namespace RealRooted.CaoFu

/-- The principal-part recurrence, with both indices reduced by one. -/
def principalCoeff : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, j =>
    ((2 * (j : ℝ)) * (2 * j + 1) * principalCoeff n (j - 1) +
        4 * (n + 1 : ℝ) ^ 2 * principalCoeff n j) /
      (2 * (n + 1 : ℝ) * (2 * (n + 1) + 1))

/-- The coefficient row has support in `0,...,n`. -/
theorem principalCoeff_eq_zero_of_lt {n j : ℕ} (h : n < j) : principalCoeff n j = 0 := by
  induction n generalizing j with
  | zero => simp [principalCoeff, show j ≠ 0 by lia]
  | succ n ih =>
    rw [principalCoeff, ih (show n < j - 1 by lia), ih (show n < j by lia)]
    simp

/-- All coefficients in the principal-part recurrence are nonnegative. -/
theorem principalCoeff_nonneg (n j : ℕ) : 0 ≤ principalCoeff n j := by
  induction n generalizing j with
  | zero => by_cases hj : j = 0 <;> simp [principalCoeff, hj]
  | succ n ih =>
    rw [principalCoeff]
    exact div_nonneg (add_nonneg (mul_nonneg (by positivity) (ih _))
      (mul_nonneg (by positivity) (ih _))) (by positivity)

/-- The highest principal-part coefficient is one. -/
@[simp] theorem principalCoeff_self (n : ℕ) : principalCoeff n n = 1 := by
  induction n with
  | zero => simp [principalCoeff]
  | succ n ih =>
    rw [principalCoeff, Nat.add_sub_cancel, ih,
      principalCoeff_eq_zero_of_lt (show n < n + 1 by lia)]
    have hden : (2 * (n + 1 : ℝ) * (2 * (n + 1) + 1)) ≠ 0 := by positivity
    rw [div_eq_iff hden]
    push_cast
    ring

/-- Every coefficient within the principal part is strictly positive. -/
theorem principalCoeff_pos {n j : ℕ} (hj : j ≤ n) : 0 < principalCoeff n j := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := by lia
    subst j
    simp [principalCoeff]
  | succ n ih =>
    rw [principalCoeff]
    apply div_pos _ (by positivity)
    by_cases hzero : j = 0
    · subst j
      simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
      exact mul_pos (by positivity) (ih (by lia))
    · have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by lia)
      exact add_pos_of_pos_of_nonneg
        (mul_pos (by positivity) (ih (show j - 1 ≤ n by lia)))
        (mul_nonneg (by positivity) (principalCoeff_nonneg n j))

end RealRooted.CaoFu
