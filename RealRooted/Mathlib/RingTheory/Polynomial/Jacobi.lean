/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic

/-!
# Shifted Jacobi polynomials

This file defines the finite shifted Jacobi polynomial
`shiftedJacobi n α β = P_n^(α,β)(1 - 2X)` over `ℝ`.  The definition is an
explicit finite coefficient sum using generalized binomial coefficients, so
none of its algebraic properties depends on convergence of a hypergeometric
series.

The main results give its coefficients, degree and leading coefficient,
values at zero and one, derivative identity, and shifted Jacobi differential
equation.
-/

@[expose] public section

open Nat Finset

namespace Polynomial

/-- The shifted Jacobi polynomial `P_n^(α,β)(1 - 2X)`, defined by its finite
coefficient expansion. -/
noncomputable def shiftedJacobi (n : ℕ) (α β : ℝ) : ℝ[X] :=
  ∑ k ∈ range (n + 1),
    C ((-1 : ℝ) ^ k * Ring.choose (n + α) (n - k) *
      Ring.choose (n + α + β + k) k) * X ^ k

/-- The coefficient formula for the shifted Jacobi polynomial. -/
theorem coeff_shiftedJacobi (n k : ℕ) (α β : ℝ) :
    (shiftedJacobi n α β).coeff k =
      if k ≤ n then
        (-1 : ℝ) ^ k * Ring.choose (n + α) (n - k) *
          Ring.choose (n + α + β + k) k
      else 0 := by
  rw [shiftedJacobi, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases h : k ≤ n
  · simp [h, Nat.lt_succ_iff.mpr h]
  · simp [h, Nat.lt_succ_iff.not.mpr h]

private lemma ring_choose_pos {x : ℝ} {n : ℕ} (h : (n : ℝ) - 1 < x) :
    0 < Ring.choose x n := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  apply mul_pos
  · positivity
  · rw [← eval₂_smulOneHom_eq_smeval]
    rw [← eval_map]
    simpa using descPochhammer_pos h

private lemma leading_choose_pos (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    0 < Ring.choose (n + α + β + n) n := by
  cases n with
  | zero => simp
  | succ n =>
      apply ring_choose_pos
      push_cast
      linarith

/-- For Jacobi parameters greater than `-1`, `shiftedJacobi n α β` has degree
exactly `n`. -/
@[simp]
theorem natDegree_shiftedJacobi (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobi n α β).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    simp [coeff_shiftedJacobi, Nat.not_le_of_lt hk]
  · simp [coeff_shiftedJacobi, (leading_choose_pos n hα hβ).ne']

/-- The leading coefficient of `shiftedJacobi n α β` for Jacobi parameters
greater than `-1`. -/
theorem leadingCoeff_shiftedJacobi (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobi n α β).leadingCoeff =
      (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n := by
  rw [leadingCoeff, natDegree_shiftedJacobi n hα hβ]
  simp [coeff_shiftedJacobi]

private lemma choose_neg_real (a : ℝ) (k : ℕ) :
    Ring.choose (-a) k = (-1 : ℝ) ^ k * Ring.choose (a + k - 1) k := by
  rw [Ring.choose_neg]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]

private lemma alternating_choose_sum (n : ℕ) (α β : ℝ) :
    ∑ k ∈ range (n + 1),
        (-1 : ℝ) ^ k * Ring.choose (n + α) (n - k) *
          Ring.choose (n + α + β + k) k =
      (-1 : ℝ) ^ n * Ring.choose (n + β) n := by
  calc
    _ = ∑ k ∈ range (n + 1),
        Ring.choose (-(n + α + β + 1)) k * Ring.choose (n + α) (n - k) := by
      apply sum_congr rfl
      intro k hk
      rw [choose_neg_real]
      have harg :
          (n : ℝ) + α + β + 1 + k - 1 = n + α + β + k := by ring
      rw [harg]
      ring
    _ = ∑ ij ∈ antidiagonal n,
        Ring.choose (-(n + α + β + 1)) ij.1 * Ring.choose (n + α) ij.2 := by
      simpa [Nat.succ_eq_add_one] using
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => Ring.choose (-(n + α + β + 1)) i * Ring.choose (n + α) j)
          n).symm
    _ = Ring.choose (-(n + α + β + 1) + (n + α)) n :=
      (Ring.add_choose_eq n (Commute.all _ _)).symm
    _ = _ := by
      rw [show -(n + α + β + 1) + (n + α) = -(β + 1) by ring]
      rw [choose_neg_real]
      congr 2
      ring

/-- The value of `shiftedJacobi n α β` at the left endpoint. -/
@[simp]
theorem shiftedJacobi_eval_zero (n : ℕ) (α β : ℝ) :
    (shiftedJacobi n α β).eval 0 = Ring.choose (n + α) n := by
  rw [← coeff_zero_eq_eval_zero, coeff_shiftedJacobi]
  simp

/-- The value of `shiftedJacobi n α β` at the right endpoint. -/
@[simp]
theorem shiftedJacobi_eval_one (n : ℕ) (α β : ℝ) :
    (shiftedJacobi n α β).eval 1 =
      (-1 : ℝ) ^ n * Ring.choose (n + β) n := by
  rw [show (shiftedJacobi n α β).eval 1 =
      ∑ k ∈ range (n + 1),
        (-1 : ℝ) ^ k * Ring.choose (n + α) (n - k) *
          Ring.choose (n + α + β + k) k by
    simp only [shiftedJacobi, eval_finsetSum, eval_mul, eval_C, eval_pow,
      eval_X, one_pow, mul_one]]
  exact alternating_choose_sum n α β

private lemma succ_mul_choose_add (x : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose (x + k) (k + 1) =
      x * Ring.choose (x + k) k := by
  have h := Ring.choose_smul_choose (R := ℝ) (x + k) (n := k + 1) (k := k) (by lia)
  have hsub : k + 1 - k = 1 := by lia
  simp only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    hsub, Ring.choose_one_right] at h
  nlinarith [h]

/-- The derivative of a shifted Jacobi polynomial is a scalar multiple of the
shifted Jacobi polynomial with both parameters incremented. -/
theorem derivative_shiftedJacobi (n : ℕ) (α β : ℝ) :
    (shiftedJacobi (n + 1) α β).derivative =
      C (-(n + α + β + 2)) * shiftedJacobi n (α + 1) (β + 1) := by
  ext k
  rw [coeff_derivative]
  simp only [coeff_C_mul]
  by_cases hk : k ≤ n
  · rw [coeff_shiftedJacobi, if_pos (Nat.succ_le_succ hk),
      coeff_shiftedJacobi, if_pos hk]
    have hr := succ_mul_choose_add (n + α + β + 2) k
    rw [show (n + 1 : ℕ) - (k + 1) = n - k by lia]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [show (n : ℝ) + 1 + α = n + (α + 1) by ring]
    rw [show (n : ℝ) + (α + 1) + β + (k + 1) =
      (n + α + β + 2) + k by ring]
    rw [show (n : ℝ) + (α + 1) + (β + 1) + k =
      (n + α + β + 2) + k by ring]
    rw [pow_succ]
    linear_combination
      ((-1 : ℝ) ^ k * -1 * Ring.choose (n + (α + 1)) (n - k)) * hr
  · rw [coeff_shiftedJacobi,
      if_neg (Nat.not_le.mpr (Nat.lt_succ_iff.mpr (Nat.lt_of_not_ge hk))),
      coeff_shiftedJacobi, if_neg hk]
    simp

private lemma succ_mul_choose_succ_add (x : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose (x + k + 1) (k + 1) =
      (x + k + 1) * Ring.choose (x + k) k := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [descPochhammer_succ_left]
  simp only [smeval_mul, smeval_X, pow_one, smeval_comp]
  have heval :
      ((X - 1 : Polynomial ℤ).smeval (x + k + 1)) = x + k := by
    simp [smeval_sub]
  rw [heval]
  norm_num only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private lemma coeff_succ_relation (n k : ℕ) (α β : ℝ) (hk : k < n) :
    (k + 1 : ℝ) * (k + α + 1) * (shiftedJacobi n α β).coeff (k + 1) =
      -((n - k : ℕ) : ℝ) * (n + α + β + k + 1) *
        (shiftedJacobi n α β).coeff k := by
  rw [coeff_shiftedJacobi n (k + 1), coeff_shiftedJacobi n k]
  rw [if_pos hk.le, if_pos (Nat.succ_le_iff.mpr hk)]
  have hfirst := succ_mul_choose_add (α + k + 1) (n - k - 1)
  have hsecond := succ_mul_choose_succ_add (n + α + β) k
  have hsub : n - k - 1 + 1 = n - k := by lia
  have htop : α + k + 1 + (n - k - 1 : ℕ) = (n : ℝ) + α := by
    rw [Nat.cast_sub (by lia : 1 ≤ n - k), Nat.cast_sub hk.le]
    push_cast
    ring
  norm_num only [Nat.cast_add, Nat.cast_one] at hfirst hsecond ⊢
  rw [hsub, htop] at hfirst
  have hcast : ((n - k - 1 : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hfirst' :
      (k + α + 1) * Ring.choose (n + α) (n - k - 1) =
        ((n - k : ℕ) : ℝ) * Ring.choose (n + α) (n - k) := by
    calc
      _ = (α + k + 1) * Ring.choose (n + α) (n - k - 1) := by ring
      _ = (((n - k - 1 : ℕ) : ℝ) + 1) * Ring.choose (n + α) (n - k) :=
        hfirst.symm
      _ = _ := by rw [hcast]
  rw [show n - (k + 1) = n - k - 1 by lia]
  have harg : (n : ℝ) + α + β + ((k : ℝ) + 1) =
      n + α + β + k + 1 := by ring
  rw [harg, pow_succ]
  calc
    _ = (-1 : ℝ) ^ k * -1 *
        ((k + α + 1) * Ring.choose (n + α) (n - k - 1)) *
        ((k + 1) * Ring.choose (n + α + β + k + 1) (k + 1)) := by ring
    _ = (-1 : ℝ) ^ k * -1 *
        (((n - k : ℕ) : ℝ) * Ring.choose (n + α) (n - k)) *
        ((n + α + β + k + 1) * Ring.choose (n + α + β + k) k) := by
      rw [hfirst', hsecond]
    _ = _ := by ring

private lemma coeff_jacobiOperator (p : ℝ[X]) (α β l : ℝ) (k : ℕ) :
    (X * (1 - X) * p.derivative.derivative +
      (C (α + 1) - C (α + β + 2) * X) * p.derivative +
      C l * p).coeff k =
      (k + 1 : ℝ) * (k + α + 1) * p.coeff (k + 1) +
        (l - k * (k + α + β + 1)) * p.coeff k := by
  rw [show X * (1 - X) * p.derivative.derivative +
      (C (α + 1) - C (α + β + 2) * X) * p.derivative + C l * p =
    X * p.derivative.derivative - X * (X * p.derivative.derivative) +
      C (α + 1) * p.derivative - C (α + β + 2) * (X * p.derivative) +
      C l * p by ring]
  cases k with
  | zero =>
      simp [coeff_derivative]
  | succ k =>
      simp only [coeff_add, coeff_sub, coeff_C_mul]
      rw [coeff_X_mul, coeff_X_mul, coeff_X_mul]
      cases k with
      | zero =>
          simp [coeff_derivative]
          ring
      | succ k =>
          rw [coeff_X_mul]
          simp [coeff_derivative]
          ring

/-- The shifted Jacobi differential equation
`X(1-X)y'' + (α+1-(α+β+2)X)y' + n(n+α+β+1)y = 0`. -/
theorem shiftedJacobi_differential_equation (n : ℕ) (α β : ℝ) :
    X * (1 - X) * (shiftedJacobi n α β).derivative.derivative +
      (C (α + 1) - C (α + β + 2) * X) * (shiftedJacobi n α β).derivative +
      C (n * (n + α + β + 1)) * shiftedJacobi n α β = 0 := by
  ext k
  rw [coeff_jacobiOperator]
  simp only [coeff_zero]
  rcases lt_trichotomy k n with hk | rfl | hk
  · have hr := coeff_succ_relation n k α β hk
    have hscalar :
        (n : ℝ) * (n + α + β + 1) - k * (k + α + β + 1) =
          ((n - k : ℕ) : ℝ) * (n + α + β + k + 1) := by
      rw [Nat.cast_sub hk.le]
      ring
    rw [hscalar]
    linear_combination hr
  · simp [coeff_shiftedJacobi]
  · rw [coeff_shiftedJacobi n (k + 1), coeff_shiftedJacobi n k]
    rw [if_neg (Nat.not_le.mpr (hk.trans_le (Nat.le_succ k))),
      if_neg (Nat.not_le.mpr hk)]
    simp

end Polynomial
