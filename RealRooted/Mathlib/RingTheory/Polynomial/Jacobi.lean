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
values at zero and one, derivative identity, shifted Jacobi differential
equation, and monic three-term recurrence with positive subdiagonal
coefficients when both parameters exceed `-1`.
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

@[simp]
theorem shiftedJacobi_zero (α β : ℝ) :
    shiftedJacobi 0 α β = 1 := by
  ext k
  cases k <;> simp [coeff_shiftedJacobi, Polynomial.coeff_one]

/-- A generalized real binomial coefficient is positive above its largest
possible zero. -/
theorem ring_choose_pos {x : ℝ} {n : ℕ} (h : (n : ℝ) - 1 < x) :
    0 < Ring.choose x n := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  apply mul_pos
  · positivity
  · rw [← eval₂_smulOneHom_eq_smeval]
    rw [← eval_map]
    simpa using descPochhammer_pos h

private lemma ring_choose_two (x : ℝ) :
    Ring.choose x 2 = x * (x - 1) / 2 := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  norm_num [descPochhammer_succ_left, smeval_mul, smeval_X, smeval_comp,
    smeval_sub, smeval_one]
  ring

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

/-- Every iterated derivative of a shifted Jacobi polynomial is a nonzero
scalar multiple of the shifted Jacobi polynomial with shifted parameters. -/
theorem exists_iterate_derivative_shiftedJacobi_eq_C_mul
    (n d : ℕ) {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (hd : d ≤ n) :
    ∃ c : ℝ, c ≠ 0 ∧
      (derivative^[d]) (shiftedJacobi n α β) =
        C c * shiftedJacobi (n - d) (α + d) (β + d) := by
  induction d with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ d ih =>
      have hdle : d ≤ n := by lia
      obtain ⟨c, hc, hcder⟩ := ih hdle
      let factor : ℝ :=
        -(((n - (d + 1) : ℕ) : ℝ) + (α + d) + (β + d) + 2)
      have hfactor_pos : 0 < -factor := by
        dsimp only [factor]
        have hn0 : 0 ≤ ((n - (d + 1) : ℕ) : ℝ) := by positivity
        have hd0 : 0 ≤ (d : ℝ) := by positivity
        linarith
      refine ⟨c * factor, mul_ne_zero hc (by linarith), ?_⟩
      have hdegree : n - d = n - (d + 1) + 1 := by lia
      have hderivative := derivative_shiftedJacobi
        (n - (d + 1)) (α + d) (β + d)
      have hαshift : α + (d + 1 : ℕ) = α + d + 1 := by
        push_cast
        ring
      have hβshift : β + (d + 1 : ℕ) = β + d + 1 := by
        push_cast
        ring
      rw [Function.iterate_succ_apply', hcder, derivative_C_mul, hdegree,
        hderivative, ← mul_assoc, ← C_mul, hαshift, hβshift]

private lemma eq_of_derivative_eq_of_eval_zero_eq {p q : ℝ[X]}
    (hderivative : p.derivative = q.derivative)
    (heval : p.eval 0 = q.eval 0) :
    p = q := by
  ext k
  cases k with
  | zero => simpa [coeff_zero_eq_eval_zero] using heval
  | succ k =>
      have hcoeff := congrArg (fun r : ℝ[X] => r.coeff k) hderivative
      simp only [coeff_derivative] at hcoeff
      have hk : 0 < (k : ℝ) + 1 := by positivity
      nlinarith

/-- Reflection symmetry for shifted Jacobi polynomials. -/
theorem shiftedJacobi_reflection (n : ℕ) (α β : ℝ) :
    shiftedJacobi n α β =
      C ((-1 : ℝ) ^ n) * (shiftedJacobi n β α).comp (1 - X) := by
  induction n generalizing α β with
  | zero => simp [shiftedJacobi]
  | succ n ih =>
      apply eq_of_derivative_eq_of_eval_zero_eq
      · rw [derivative_shiftedJacobi]
        simp only [derivative_mul, derivative_C, zero_mul, zero_add,
          derivative_comp_one_sub_X]
        rw [derivative_shiftedJacobi, ih (α + 1) (β + 1)]
        simp
        ring
      · have hsign :
            (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
          rw [← pow_add, show n + 1 + (n + 1) = 2 * (n + 1) by lia, pow_mul]
          norm_num
        simp only [shiftedJacobi_eval_zero, Nat.cast_add, Nat.cast_one, map_pow,
          map_neg, map_one, eval_mul, eval_pow, eval_neg, eval_one, eval_comp,
          eval_sub, eval_X, sub_zero, shiftedJacobi_eval_one]
        rw [← mul_assoc, hsign, one_mul]

private lemma succ_mul_ringChoose (x : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose x (k + 1) =
      x * Ring.choose (x - 1) k := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [descPochhammer_succ_left]
  simp only [smeval_mul, smeval_X, pow_one, smeval_comp, smeval_sub,
    smeval_one, one_smul]
  norm_num only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private lemma sub_mul_ringChoose (x : ℝ) (k : ℕ) :
    (x - k) * Ring.choose x k = x * Ring.choose (x - 1) k := by
  cases k with
  | zero => simp
  | succ k =>
      have hpascal := Ring.choose_succ_succ (x - 1) k
      have hsucc := succ_mul_ringChoose x k
      rw [show x - 1 + 1 = x by ring] at hpascal
      norm_num only [Nat.cast_add, Nat.cast_one] at hsucc ⊢
      linear_combination x * hpascal - hsucc

/-- The unit shift in the second Jacobi parameter, in a form relating two
degrees. -/
theorem shiftedJacobi_beta_add_one (n : ℕ) (α β : ℝ) (hn : 0 < n) :
    C (2 * n + α + β + 1) * shiftedJacobi n α β =
      C (n + α + β + 1) * shiftedJacobi n α (β + 1) +
        C (n + α) * shiftedJacobi (n - 1) α (β + 1) := by
  ext k
  simp only [coeff_C_mul, coeff_add]
  rw [coeff_shiftedJacobi n k α β, coeff_shiftedJacobi n k α (β + 1),
    coeff_shiftedJacobi (n - 1) k α (β + 1)]
  by_cases hk : k ≤ n
  · rw [if_pos hk, if_pos hk]
    by_cases hkn : k = n
    · subst k
      rw [if_neg (by lia : ¬n ≤ n - 1)]
      cases n with
      | zero => contradiction
      | succ d =>
          let t : ℝ := 2 * d + α + β + 2
          let b : ℝ := d + α + β + 2
          have hchoose :
              Ring.choose (t + 1) (d + 1) =
                Ring.choose t d + Ring.choose t (d + 1) := by
            exact Ring.choose_succ_succ t d
          have hratio :
              (d + 1 : ℝ) * Ring.choose t (d + 1) =
                b * Ring.choose t d := by
            have h := succ_mul_choose_add b d
            rw [show b + d = t by simp [t, b]; ring] at h
            exact h
          norm_num only [Nat.cast_add, Nat.cast_one, Nat.sub_self,
            Ring.choose_zero_right, mul_one, mul_zero, add_zero]
          rw [show (d : ℝ) + 1 + α + β + (d + 1) = t by simp [t]; ring,
            show (d : ℝ) + 1 + α + (β + 1) + (d + 1) = t + 1 by
              simp [t]
              ring,
            hchoose]
          simp only [t, b] at hratio ⊢
          linear_combination
            ((-1 : ℝ) ^ (d + 1)) * hratio
    · have hk_pred : k ≤ n - 1 := by lia
      rw [if_pos hk_pred]
      have hleft := succ_mul_ringChoose (n + α) (n - 1 - k)
      rw [show n - 1 - k + 1 = n - k by lia] at hleft
      have hn_one : 1 ≤ n := by lia
      have hindex : ((n - 1 - k : ℕ) : ℝ) + 1 = (n - k : ℕ) := by
        exact_mod_cast (show n - 1 - k + 1 = n - k by lia)
      rw [hindex, Nat.cast_sub hk] at hleft
      rw [show ((n - 1 : ℕ) : ℝ) + α = n + α - 1 by
        rw [Nat.cast_sub hn_one, Nat.cast_one]
        ring]
      rw [show n + α - 1 + (β + 1) + k = n + α + β + k by ring]
      rw [show n + α + (β + 1) + k = (n + α + β + k) + 1 by ring]
      cases k with
      | zero =>
          norm_num only [Nat.cast_zero, pow_zero, Ring.choose_zero_right, mul_one]
          linear_combination
            hleft
      | succ d =>
          have hright :
              (d + 1 : ℝ) *
                  Ring.choose (n + α + β + (d + 1)) (d + 1) =
                (n + α + β + 1) *
                  Ring.choose (n + α + β + (d + 1)) d := by
            convert succ_mul_choose_add (n + α + β + 1) d using 1 <;>
              ring
          rw [Ring.choose_succ_succ]
          norm_num only [Nat.cast_add, Nat.cast_one] at hleft hright ⊢
          linear_combination
            ((-1 : ℝ) ^ (d + 1) * Ring.choose (n + α + β + (d + 1)) (d + 1)) *
                hleft +
              ((-1 : ℝ) ^ (d + 1) * Ring.choose (n + α) (n - (d + 1))) *
                hright
  · rw [if_neg hk]
    have hk_pred : ¬k ≤ n - 1 := by lia
    rw [if_neg hk_pred, if_neg hk]
    simp

/-- The unit shift in the first Jacobi parameter, obtained from the second
parameter identity by reflection. -/
theorem shiftedJacobi_alpha_add_one (n : ℕ) (α β : ℝ) (hn : 0 < n) :
    C (2 * n + α + β + 1) * shiftedJacobi n α β =
      C (n + α + β + 1) * shiftedJacobi n (α + 1) β -
        C (n + β) * shiftedJacobi (n - 1) (α + 1) β := by
  have h := shiftedJacobi_beta_add_one n β α hn
  have hcomp := congrArg
    (fun p : ℝ[X] => C ((-1 : ℝ) ^ n) * p.comp (1 - X)) h
  simp only [add_comp, mul_comp, C_comp] at hcomp
  have hsign : (-1 : ℝ) ^ n = -((-1 : ℝ) ^ (n - 1)) := by
    cases n with
    | zero => contradiction
    | succ m => simp [pow_succ]
  rw [shiftedJacobi_reflection n α β,
    shiftedJacobi_reflection n (α + 1) β,
    shiftedJacobi_reflection (n - 1) (α + 1) β, hsign]
  rw [hsign] at hcomp
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat] at hcomp ⊢
  linear_combination hcomp

/-- The two-unit shift in the first Jacobi parameter. This is the shifted
form of the contiguous identity used in same-degree endpoint comparisons. -/
theorem shiftedJacobi_alpha_add_two (n : ℕ) (α β : ℝ) (hα : -1 < α) :
    C (-(n + α + 1)) * shiftedJacobi n α β =
      C (n + α + β + 2) * X * shiftedJacobi n (α + 2) β -
        (C (α + 1) + C (α + β + 2 * n + 2) * X) *
          shiftedJacobi n (α + 1) β := by
  rw [show C (n + α + β + 2) * X * shiftedJacobi n (α + 2) β =
    C (n + α + β + 2) * (X * shiftedJacobi n (α + 2) β) by ring]
  rw [show (C (α + 1) + C (α + β + 2 * n + 2) * X) *
      shiftedJacobi n (α + 1) β =
    C (α + 1) * shiftedJacobi n (α + 1) β +
      C (α + β + 2 * n + 2) * (X * shiftedJacobi n (α + 1) β) by ring]
  ext k
  cases k with
  | zero =>
      have hleft := succ_mul_ringChoose (n + α + 1) n
      have hright := succ_mul_choose_add (α + 1) n
      rw [show (n : ℝ) + α + 1 - 1 = n + α by ring] at hleft
      rw [show α + 1 + n = n + α + 1 by ring] at hright
      simp only [coeff_C_mul, coeff_sub, coeff_add]
      simp only [coeff_shiftedJacobi, if_pos (Nat.zero_le n), pow_zero,
        Ring.choose_zero_right, Nat.sub_zero, one_mul]
      have hx2 : (X * shiftedJacobi n (α + 2) β).coeff 0 = 0 := by
        rw [coeff_zero_eq_eval_zero]
        simp
      have hx1 : (X * shiftedJacobi n (α + 1) β).coeff 0 = 0 := by
        rw [coeff_zero_eq_eval_zero]
        simp
      rw [hx2, hx1]
      have hchoose :
          (n + α + 1) * Ring.choose (n + α) n =
            (α + 1) * Ring.choose (n + α + 1) n := hleft.symm.trans hright
      simp only [mul_zero, mul_one, add_zero, zero_sub]
      rw [show (n : ℝ) + (α + 1) = n + α + 1 by ring]
      simpa only [neg_mul] using congrArg Neg.neg hchoose
  | succ k =>
      simp only [coeff_C_mul, coeff_sub, coeff_add]
      simp only [coeff_X_mul]
      rcases lt_trichotomy k n with hk | rfl | hk
      · rw [coeff_shiftedJacobi n (k + 1), coeff_shiftedJacobi n k,
          coeff_shiftedJacobi n (k + 1), coeff_shiftedJacobi n k]
        rw [if_pos (Nat.succ_le_iff.mpr hk), if_pos hk.le,
          if_pos (Nat.succ_le_iff.mpr hk), if_pos hk.le]
        have hA0 := succ_mul_ringChoose (n + α + 1) (n - k - 1)
        rw [show n - k - 1 + 1 = n - k by lia,
          show (n : ℝ) + α + 1 - 1 = n + α by ring] at hA0
        have hB0 := succ_mul_choose_add (n + α + β + 1) k
        rw [show (n : ℝ) + α + β + 1 + k = n + α + β + k + 1 by ring]
          at hB0
        have hA2 := sub_mul_ringChoose (n + α + 2) (n - k)
        rw [show (n : ℝ) + α + 2 - 1 = n + α + 1 by ring] at hA2
        have hB2 := sub_mul_ringChoose (n + α + β + k + 2) k
        rw [show (n : ℝ) + α + β + k + 2 - 1 = n + α + β + k + 1 by ring]
          at hB2
        have hA1 := succ_mul_choose_add (α + k + 2) (n - k - 1)
        rw [show n - k - 1 + 1 = n - k by lia] at hA1
        have hB1 := succ_mul_ringChoose (n + α + β + k + 2) k
        rw [show (n : ℝ) + α + β + k + 2 - 1 = n + α + β + k + 1 by ring]
          at hB1
        norm_num only [Nat.cast_add, Nat.cast_one] at hA0 hB0 hA2 hB2 hA1 hB1 ⊢
        have hsub : n - (k + 1) = n - k - 1 := by lia
        have hcast : ((n - k : ℕ) : ℝ) = n - k := by
          rw [Nat.cast_sub hk.le]
        have hcastPred : ((n - k - 1 : ℕ) : ℝ) = n - k - 1 := by
          rw [Nat.cast_sub (by lia : 1 ≤ n - k), Nat.cast_sub hk.le]
          norm_num
        rw [hsub]
        rw [hcastPred] at hA0 hA1
        rw [hcast] at hA2
        rw [show α + (k : ℝ) + 2 + (n - k - 1) = n + α + 1 by ring] at hA1
        have hA0' :
            (n - k) * Ring.choose (n + α + 1) (n - k) =
              (n + α + 1) * Ring.choose (n + α) (n - k - 1) := by
          convert hA0 using 1
          ring
        have hB0' :
            (k + 1) * Ring.choose (n + α + β + k + 1) (k + 1) =
              (n + α + β + 1) * Ring.choose (n + α + β + k + 1) k := hB0
        have hA2' :
            (α + k + 2) * Ring.choose (n + α + 2) (n - k) =
              (n + α + 2) * Ring.choose (n + α + 1) (n - k) := by
          convert hA2 using 1
          ring
        have hB2' :
            (n + α + β + 2) * Ring.choose (n + α + β + k + 2) k =
              (n + α + β + k + 2) * Ring.choose (n + α + β + k + 1) k := by
          convert hB2 using 1
          ring
        have hA1' :
            (n - k) * Ring.choose (n + α + 1) (n - k) =
              (α + k + 2) * Ring.choose (n + α + 1) (n - k - 1) := by
          convert hA1 using 1
          ring
        have hB1' :
            (k + 1) * Ring.choose (n + α + β + k + 2) (k + 1) =
              (n + α + β + k + 2) *
                Ring.choose (n + α + β + k + 1) k := hB1
        have hterm0 :
            (n + α + 1) * (k + 1) * Ring.choose (n + α) (n - k - 1) *
                Ring.choose (n + α + β + k + 1) (k + 1) =
              (n - k) * (n + α + β + 1) *
                Ring.choose (n + α + 1) (n - k) *
                Ring.choose (n + α + β + k + 1) k := by
          calc
            _ = ((n + α + 1) * Ring.choose (n + α) (n - k - 1)) *
                ((k + 1) * Ring.choose (n + α + β + k + 1) (k + 1)) := by ring
            _ = ((n - k) * Ring.choose (n + α + 1) (n - k)) *
                ((n + α + β + 1) * Ring.choose (n + α + β + k + 1) k) := by
              rw [← hA0', hB0']
            _ = _ := by ring
        have hterm2 :
            (α + k + 2) * (n + α + β + 2) *
                Ring.choose (n + α + 2) (n - k) *
                Ring.choose (n + α + β + k + 2) k =
              (n + α + 2) * (n + α + β + k + 2) *
                Ring.choose (n + α + 1) (n - k) *
                Ring.choose (n + α + β + k + 1) k := by
          calc
            _ = ((α + k + 2) * Ring.choose (n + α + 2) (n - k)) *
                ((n + α + β + 2) * Ring.choose (n + α + β + k + 2) k) := by ring
            _ = ((n + α + 2) * Ring.choose (n + α + 1) (n - k)) *
                ((n + α + β + k + 2) *
                  Ring.choose (n + α + β + k + 1) k) := by
              rw [hA2', hB2']
            _ = _ := by ring
        have hterm1 :
            (k + 1) * (α + k + 2) *
                Ring.choose (n + α + 1) (n - k - 1) *
                Ring.choose (n + α + β + k + 2) (k + 1) =
              (n - k) * (n + α + β + k + 2) *
                Ring.choose (n + α + 1) (n - k) *
                Ring.choose (n + α + β + k + 1) k := by
          calc
            _ = ((α + k + 2) * Ring.choose (n + α + 1) (n - k - 1)) *
                ((k + 1) * Ring.choose (n + α + β + k + 2) (k + 1)) := by ring
            _ = ((n - k) * Ring.choose (n + α + 1) (n - k)) *
                ((n + α + β + k + 2) *
                  Ring.choose (n + α + β + k + 1) k) := by
              rw [← hA1', hB1']
            _ = _ := by ring
        have hfactor : (k + 1 : ℝ) * (α + k + 2) ≠ 0 := by
          apply mul_ne_zero
          · positivity
          · have hkNonneg : 0 ≤ (k : ℝ) := by positivity
            linarith
        apply mul_left_cancel₀ hfactor
        ring_nf at hterm0 hterm2 hterm1 ⊢
        linear_combination
          ((-1 : ℝ) ^ k * (α + k + 2)) * hterm0 -
            ((-1 : ℝ) ^ k * (k + 1)) * hterm2 -
            ((-1 : ℝ) ^ k * (α + 1)) * hterm1
      · rw [coeff_shiftedJacobi k (k + 1), coeff_shiftedJacobi k k,
          coeff_shiftedJacobi k (k + 1), coeff_shiftedJacobi k k]
        rw [if_neg (by lia), if_pos le_rfl, if_neg (by lia), if_pos le_rfl]
        have hlead := sub_mul_ringChoose (2 * k + α + β + 2) k
        rw [show (2 : ℝ) * k + α + β + 2 - 1 = 2 * k + α + β + 1 by ring]
          at hlead
        norm_num only [Nat.cast_add, Nat.cast_one, Nat.sub_self,
          Ring.choose_zero_right, mul_one, zero_mul, add_zero]
        ring_nf at hlead ⊢
        linear_combination (-((-1 : ℝ) ^ k)) * hlead
      · rw [coeff_shiftedJacobi n (k + 1), coeff_shiftedJacobi n k,
          coeff_shiftedJacobi n (k + 1), coeff_shiftedJacobi n k]
        rw [if_neg (by lia), if_neg (by lia), if_neg (by lia), if_neg (by lia)]
        ring

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

/-- Two degree-at-most-`n` solutions of the shifted Jacobi differential
equation agree if their constant coefficients agree. -/
theorem eq_of_jacobi_differential_equation
    (n : ℕ) {α β : ℝ} (hα : -1 < α) {p q : ℝ[X]}
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n)
    (hcoeff : p.coeff 0 = q.coeff 0)
    (hpode :
      X * (1 - X) * p.derivative.derivative +
        (C (α + 1) - C (α + β + 2) * X) * p.derivative +
        C (n * (n + α + β + 1)) * p = 0)
    (hqode :
      X * (1 - X) * q.derivative.derivative +
        (C (α + 1) - C (α + β + 2) * X) * q.derivative +
        C (n * (n + α + β + 1)) * q = 0) :
    p = q := by
  apply Polynomial.ext
  intro k
  induction k with
  | zero => exact hcoeff
  | succ k ih =>
      by_cases hk : k < n
      · have hpcoeff := congrArg (fun r : ℝ[X] => r.coeff k) hpode
        have hqcoeff := congrArg (fun r : ℝ[X] => r.coeff k) hqode
        rw [coeff_jacobiOperator, coeff_zero, ih] at hpcoeff
        rw [coeff_jacobiOperator, coeff_zero] at hqcoeff
        have hkα : 0 < (k : ℝ) + α + 1 := by
          have hk0 : 0 ≤ (k : ℝ) := by positivity
          linarith
        have hfactor : 0 < ((k : ℝ) + 1) * (k + α + 1) := by
          exact mul_pos (by positivity) hkα
        nlinarith
      · have hpzero : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        have hqzero : q.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        rw [hpzero, hqzero]

/-- The monic normalization of the shifted Jacobi polynomial. -/
noncomputable def shiftedJacobiMonic (n : ℕ) (α β : ℝ) : ℝ[X] :=
  C (((-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n)⁻¹) *
    shiftedJacobi n α β

/-- Reflection symmetry for the monic shifted Jacobi polynomial. -/
theorem shiftedJacobiMonic_reflection (n : ℕ) (α β : ℝ) :
    shiftedJacobiMonic n α β =
      C ((-1 : ℝ) ^ n) * (shiftedJacobiMonic n β α).comp (1 - X) := by
  rw [shiftedJacobiMonic, shiftedJacobiMonic, shiftedJacobi_reflection]
  simp only [mul_comp, C_comp, ← mul_assoc, ← C_mul]
  congr 1
  congr 1
  ring_nf

/-- The coefficient formula for the monic shifted Jacobi polynomial. -/
theorem coeff_shiftedJacobiMonic (n k : ℕ) (α β : ℝ) :
    (shiftedJacobiMonic n α β).coeff k =
      (((-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n)⁻¹) *
        (if k ≤ n then
          (-1 : ℝ) ^ k * Ring.choose (n + α) (n - k) *
            Ring.choose (n + α + β + k) k
        else 0) := by
  rw [shiftedJacobiMonic, coeff_C_mul, coeff_shiftedJacobi]

/-- The monic shifted Jacobi polynomial of degree zero is one. -/
@[simp]
theorem shiftedJacobiMonic_zero (α β : ℝ) :
    shiftedJacobiMonic 0 α β = 1 := by
  ext k
  cases k <;> simp [coeff_shiftedJacobiMonic, Polynomial.coeff_one]

/-- The monic shifted Jacobi polynomial of degree one. -/
theorem shiftedJacobiMonic_one (α β : ℝ) (h : α + β + 2 ≠ 0) :
    shiftedJacobiMonic 1 α β = X - C ((α + 1) / (α + β + 2)) := by
  have hneg : -2 - α - β ≠ 0 := by
    intro hzero
    apply h
    linarith
  ext k
  cases k with
  | zero =>
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      rw [coeff_shiftedJacobiMonic]
      norm_num [Ring.choose_one_right, div_eq_mul_inv]
      have hden : -1 + (-β + (-α + -1)) = -2 - α - β := by ring
      rw [hden]
      have hinv : (-2 - α - β)⁻¹ = -(α + β + 2)⁻¹ := by
        rw [show -2 - α - β = -(α + β + 2) by ring, inv_neg]
      rw [hinv]
      field_simp [h]
      ring
  | succ k =>
      cases k with
      | zero =>
          simp only [coeff_sub, coeff_C_succ, sub_zero]
          rw [coeff_shiftedJacobiMonic]
          norm_num [Ring.choose_one_right]
          have hden : -1 + (-β + (-α + -1)) = -2 - α - β := by ring
          rw [hden, inv_mul_cancel₀ hneg]
      | succ k =>
          simp [coeff_shiftedJacobiMonic, Polynomial.coeff_X]

/-- The normalization really is monic for Jacobi parameters greater than
`-1`. -/
theorem monic_shiftedJacobiMonic (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobiMonic n α β).Monic := by
  have hchoose := (leading_choose_pos n hα hβ).ne'
  have hscale : (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n ≠ 0 :=
    mul_ne_zero (pow_ne_zero n (by norm_num)) hchoose
  rw [Monic.def, shiftedJacobiMonic,
    leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero hscale)),
    leadingCoeff_shiftedJacobi n hα hβ]
  exact inv_mul_cancel₀ hscale

/-- The monic shifted Jacobi polynomial has its indexed degree. -/
@[simp]
theorem natDegree_shiftedJacobiMonic (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobiMonic n α β).natDegree = n := by
  have hscale : (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n ≠ 0 :=
    mul_ne_zero (pow_ne_zero n (by norm_num)) (leading_choose_pos n hα hβ).ne'
  rw [shiftedJacobiMonic, natDegree_C_mul (inv_ne_zero hscale),
    natDegree_shiftedJacobi n hα hβ]

/-- The diagonal coefficient in the monic shifted-Jacobi recurrence. -/
noncomputable def shiftedJacobiDiag (n : ℕ) (α β : ℝ) : ℝ :=
  if n = 0 then
    (α + 1) / (α + β + 2)
  else
    (1 - (β ^ 2 - α ^ 2) /
      ((2 * n + α + β) * (2 * n + α + β + 2))) / 2

/-- The subdiagonal coefficient in the monic shifted-Jacobi recurrence. -/
noncomputable def shiftedJacobiSubdiag (n : ℕ) (α β : ℝ) : ℝ :=
  if n = 0 then 0
  else if n = 1 then
    (1 + α) * (1 + β) / ((α + β + 2) ^ 2 * (α + β + 3))
  else
    n * (n + α) * (n + β) * (n + α + β) /
      ((2 * n + α + β) ^ 2 *
        (2 * n + α + β - 1) * (2 * n + α + β + 1))

private lemma succ_mul_choose_succ (r : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose (r + 1) (k + 1) =
      (r + 1) * Ring.choose r k := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, descPochhammer_succ_left, smeval_mul,
    smeval_X, pow_one, smeval_comp, smeval_sub, smeval_one, pow_zero,
    one_smul, add_sub_cancel_right, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

private lemma sub_mul_choose_add_one (r : ℝ) (k : ℕ) :
    (r + 1 - k) * Ring.choose (r + 1) k =
      (r + 1) * Ring.choose r k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [Ring.choose_succ_succ]
      have h := Ring.choose_smul_choose (R := ℝ) r (n := k + 1) (k := k) (by lia)
      simp only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one, Nat.add_sub_cancel_left, Ring.choose_one_right] at h
      push_cast at h ⊢
      linear_combination -h

private lemma succ_mul_ringChoose_same (x : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * Ring.choose x (k + 1) =
      (x - k) * Ring.choose x k := by
  have hleft := succ_mul_ringChoose x k
  have hright := sub_mul_choose_add_one (x - 1) k
  calc
    (k + 1 : ℝ) * Ring.choose x (k + 1) =
        x * Ring.choose (x - 1) k := hleft
    _ = (x - k) * Ring.choose x k := by
      convert hright.symm using 1 <;> ring

private lemma coeff_X_mul_derivative_eq (f : ℝ[X]) (k : ℕ) :
    (X * f.derivative).coeff k = k * f.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring

/-- Raising the degree while lowering the second Jacobi parameter is a
first-order differential operation. -/
theorem shiftedJacobi_degree_add_one_beta_sub_one (n : ℕ) (α β : ℝ) :
    X * (1 - X) * (shiftedJacobi n α β).derivative +
        (C (n + α + 1) - C (n + α + β + 1) * X) *
          shiftedJacobi n α β =
      C ((n + 1 : ℕ) : ℝ) * shiftedJacobi (n + 1) α (β - 1) := by
  let f := shiftedJacobi n α β
  let g := shiftedJacobi (n + 1) α (β - 1)
  have hform :
      X * (1 - X) * f.derivative +
          (C (n + α + 1) - C (n + α + β + 1) * X) * f =
        X * f.derivative - X * (X * f.derivative) +
          C (n + α + 1) * f - C (n + α + β + 1) * (X * f) := by
    ring
  apply Polynomial.ext
  intro k
  rw [hform]
  cases k with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_X_mul_zero, coeff_C_mul]
      dsimp only [f, g]
      rw [coeff_shiftedJacobi, if_pos (Nat.zero_le n),
        coeff_shiftedJacobi, if_pos (Nat.zero_le (n + 1))]
      norm_num only [Nat.cast_zero, pow_zero, Ring.choose_zero_right, mul_one,
        Nat.sub_zero, Nat.zero_add, Nat.cast_add, Nat.cast_one]
      have hchoose := succ_mul_choose_succ (n + α) n
      convert hchoose.symm using 1 <;> ring
  | succ k =>
      simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul,
        coeff_derivative, coeff_X_mul_derivative_eq]
      push_cast
      dsimp only [f, g]
      by_cases hk : k + 1 ≤ n
      · rw [coeff_shiftedJacobi, if_pos hk, coeff_shiftedJacobi,
          if_pos (by lia : k ≤ n), coeff_shiftedJacobi,
          if_pos (by lia : k + 1 ≤ n + 1)]
        have hfirst := succ_mul_ringChoose_same (n + α) (n - (k + 1))
        have hsecond := succ_mul_choose_succ_add (n + α + β) k
        have hpascal := Ring.choose_succ_succ (n + α) (n - (k + 1))
        rw [show n - (k + 1) + 1 = n - k by lia] at hfirst
        rw [Nat.cast_sub hk] at hfirst
        norm_num only [Nat.cast_add, Nat.cast_one, pow_succ] at hfirst hsecond ⊢
        have htop : (n : ℝ) + 1 + α = n + α + 1 := by ring
        have hsecondTop :
            (n : ℝ) + α + 1 + (β - 1) + (k + 1) =
              n + α + β + (k + 1) := by ring
        rw [htop, hsecondTop]
        rw [show n + 1 - (k + 1) = n - (k + 1) + 1 by lia,
          hpascal]
        rw [show n - (k + 1) + 1 = n - k by lia]
        have hfirst' :
            ((n : ℝ) - k) * Ring.choose (n + α) (n - k) =
              (α + k + 1) * Ring.choose (n + α) (n - (k + 1)) := by
          convert hfirst using 1 <;> ring
        have hsecond' :
            (k + 1 : ℝ) * Ring.choose (n + α + β + (k + 1)) (k + 1) =
              (n + α + β + k + 1) *
                Ring.choose (n + α + β + k) k := by
          convert hsecond using 1
          · ring
        have hfirstScaled := congrArg
          (((-1 : ℝ) ^ k *
            Ring.choose (n + α + β + (k + 1)) (k + 1)) * ·) hfirst'
        have hsecondScaled := congrArg
          (((-1 : ℝ) ^ k * Ring.choose (n + α) (n - k)) * ·) hsecond'
        ring_nf at hfirstScaled hsecondScaled ⊢
        linarith
      · by_cases hboundary : k + 1 = n + 1
        · have hkEq : k = n := by lia
          subst k
          rw [coeff_shiftedJacobi, if_neg (by lia : ¬n + 1 ≤ n),
            coeff_shiftedJacobi, if_pos le_rfl, coeff_shiftedJacobi,
            if_pos le_rfl]
          have hchoose := succ_mul_choose_succ_add (n + α + β) n
          norm_num only [Nat.cast_add, Nat.cast_one, Nat.sub_self,
            Ring.choose_zero_right, pow_succ, zero_mul, add_zero]
          have htop :
              (n : ℝ) + 1 + α + (β - 1) + (n + 1) =
                n + α + β + n + 1 := by ring
          rw [htop]
          linear_combination ((-1 : ℝ) ^ n) * hchoose
        · have hlarge : n + 1 < k + 1 := by lia
          rw [coeff_shiftedJacobi, if_neg (by lia : ¬k + 1 ≤ n),
            coeff_shiftedJacobi, if_neg (by lia : ¬k ≤ n),
            coeff_shiftedJacobi, if_neg (by lia : ¬k + 1 ≤ n + 1)]
          ring

private lemma coeff_shiftedJacobi_succ_degree
    (n k : ℕ) (α β : ℝ) (hk : k ≤ n) :
    ((n + 1 - k : ℕ) : ℝ) * (n + α + β + 1) *
        (shiftedJacobi (n + 1) α β).coeff k =
      (n + α + 1) * (n + α + β + k + 1) *
        (shiftedJacobi n α β).coeff k := by
  rw [coeff_shiftedJacobi, if_pos (by lia), coeff_shiftedJacobi, if_pos hk]
  have hsub : n + 1 - k = n - k + 1 := by lia
  rw [hsub]
  have hfirst := succ_mul_choose_succ (n + α) (n - k)
  have hsecond := sub_mul_choose_add_one (n + α + β + k) k
  norm_num only [Nat.cast_add, Nat.cast_one] at hfirst hsecond ⊢
  have htop : (n : ℝ) + 1 + α = n + α + 1 := by ring
  have hchoose : (n : ℝ) + α + 1 + β + k = n + α + β + k + 1 := by ring
  rw [htop, hchoose]
  have hsecond' :
      (n + α + β + 1) * Ring.choose (n + α + β + k + 1) k =
        (n + α + β + k + 1) * Ring.choose (n + α + β + k) k := by
    convert hsecond using 1 ; ring
  calc
    _ = (-1 : ℝ) ^ k *
        ((((n - k : ℕ) : ℝ) + 1) *
          Ring.choose ((n : ℝ) + α + 1) (n - k + 1)) *
        ((n + α + β + 1) *
          Ring.choose (n + α + β + k + 1) k) := by ring
    _ = (-1 : ℝ) ^ k *
        ((n + α + 1) * Ring.choose (n + α) (n - k)) *
        ((n + α + β + k + 1) *
          Ring.choose (n + α + β + k) k) := by
      rw [hfirst, hsecond']
    _ = _ := by ring

private lemma coeff_shiftedJacobi_pred_degree
    (n k : ℕ) (α β : ℝ) (hn : 1 ≤ n) (hk : k < n) :
    (n + α) * (n + α + β + k) *
        (shiftedJacobi (n - 1) α β).coeff k =
      ((n - k : ℕ) : ℝ) * (n + α + β) *
        (shiftedJacobi n α β).coeff k := by
  rw [coeff_shiftedJacobi, if_pos (by lia), coeff_shiftedJacobi, if_pos hk.le]
  have hfirst := succ_mul_choose_succ ((n - 1 : ℕ) + α) (n - 1 - k)
  have hsecond := sub_mul_choose_add_one ((n - 1 : ℕ) + α + β + k) k
  have hnksub : n - 1 - k + 1 = n - k := by lia
  rw [hnksub] at hfirst
  rw [Nat.cast_sub hn] at hfirst hsecond ⊢
  norm_num only [Nat.cast_one] at hfirst hsecond ⊢
  have hcastsub : ((n - k : ℕ) : ℝ) = ((n - 1 - k : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnksub.symm
  have hfirst' :
      ((n - k : ℕ) : ℝ) * Ring.choose (n + α) (n - k) =
        (n + α) * Ring.choose (n - 1 + α) (n - 1 - k) := by
    rw [hcastsub]
    convert hfirst using 1 <;> ring
  have hsecond' :
      (n + α + β) * Ring.choose (n + α + β + k) k =
        (n + α + β + k) * Ring.choose (n - 1 + α + β + k) k := by
    convert hsecond using 1 <;> ring
  calc
    _ = (-1 : ℝ) ^ k *
        ((n + α) * Ring.choose (n - 1 + α) (n - 1 - k)) *
        ((n + α + β + k) *
          Ring.choose (n - 1 + α + β + k) k) := by ring
    _ = (-1 : ℝ) ^ k *
        (((n - k : ℕ) : ℝ) * Ring.choose (n + α) (n - k)) *
        ((n + α + β) * Ring.choose (n + α + β + k) k) := by
      rw [hfirst', hsecond']
    _ = _ := by ring

private lemma leading_choose_succ_degree (n : ℕ) (α β : ℝ) :
    (n + 1) * (n + α + β + 1) *
        Ring.choose (n + 1 + α + β + (n + 1)) (n + 1) =
      (2 * n + α + β + 2) * (2 * n + α + β + 1) *
        Ring.choose (n + α + β + n) n := by
  have hfirst := succ_mul_choose_succ (2 * n + α + β + 1) n
  have hsecond := sub_mul_choose_add_one (2 * n + α + β) n
  have hfirst' :
      (n + 1) * Ring.choose (2 * n + α + β + 2) (n + 1) =
        (2 * n + α + β + 2) * Ring.choose (2 * n + α + β + 1) n := by
    convert hfirst using 1 <;> ring
  have hsecond' :
      (n + α + β + 1) * Ring.choose (2 * n + α + β + 1) n =
        (2 * n + α + β + 1) * Ring.choose (2 * n + α + β) n := by
    convert hsecond using 1 ; ring
  calc
    _ = ((n + 1) * Ring.choose (2 * n + α + β + 2) (n + 1)) *
        (n + α + β + 1) := by ring
    _ = ((2 * n + α + β + 2) *
          Ring.choose (2 * n + α + β + 1) n) *
        (n + α + β + 1) := by rw [hfirst']
    _ = (2 * n + α + β + 2) *
        ((n + α + β + 1) * Ring.choose (2 * n + α + β + 1) n) := by ring
    _ = _ := by rw [hsecond']; ring

private lemma leading_scale_succ_degree (n : ℕ) (α β : ℝ) :
    (n + 1) * (n + α + β + 1) *
        ((-1 : ℝ) ^ (n + 1) *
          Ring.choose (n + 1 + α + β + (n + 1)) (n + 1)) =
      -(2 * n + α + β + 2) * (2 * n + α + β + 1) *
        ((-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n) := by
  rw [pow_succ]
  linear_combination (-((-1 : ℝ) ^ n)) * leading_choose_succ_degree n α β

/-- A denominator-free three-term recurrence for shifted Jacobi polynomials.
This form is convenient for coefficient algebra; `shiftedJacobiMonic_recurrence`
below is the standard monic Favard form. -/
theorem shiftedJacobi_recurrence_raw (n : ℕ) (α β : ℝ)
    (hn : 2 ≤ n) (hα : -1 < α) (hβ : -1 < β) :
    C (2 * (n + 1) * (n + α + β + 1) * (2 * n + α + β)) *
        shiftedJacobi (n + 1) α β =
      C (-2 * (2 * n + α + β + 2) * (2 * n + α + β + 1) *
          (2 * n + α + β)) * (X * shiftedJacobi n α β) +
        C ((2 * n + α + β + 1) *
          ((2 * n + α + β) * (2 * n + α + β + 2) - β ^ 2 + α ^ 2)) *
            shiftedJacobi n α β -
          C (2 * (2 * n + α + β + 2) * (n + α) * (n + β)) *
            shiftedJacobi (n - 1) α β := by
  ext k
  simp only [coeff_C_mul, coeff_add, coeff_sub]
  by_cases hk0 : k = 0
  · subst k
    have hcoeffX : (X * shiftedJacobi n α β).coeff 0 = 0 := by simp
    rw [hcoeffX]
    have hup := coeff_shiftedJacobi_succ_degree n 0 α β (by lia)
    have hdown := coeff_shiftedJacobi_pred_degree n 0 α β (by lia) (by lia)
    norm_num at hup hdown
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hna : (n + α : ℝ) ≠ 0 := by linarith
    have hcommonUp : (n + α + β + 1 : ℝ) ≠ 0 := by linarith
    have hcommonDown : (n + α + β : ℝ) ≠ 0 := by linarith
    have hupCancel :
        (n + 1 : ℝ) * (shiftedJacobi (n + 1) α β).coeff 0 =
          (n + α + 1) * (shiftedJacobi n α β).coeff 0 := by
      apply mul_right_cancel₀ hcommonUp
      calc
        _ = (n + 1) * (n + α + β + 1) *
            (shiftedJacobi (n + 1) α β).coeff 0 := by ring
        _ = _ := hup
        _ = ((n + α + 1) * (shiftedJacobi n α β).coeff 0) *
            (n + α + β + 1) := by ring
    have hdownCancel :
        (n + α) * (shiftedJacobi (n - 1) α β).coeff 0 =
          n * (shiftedJacobi n α β).coeff 0 := by
      apply mul_right_cancel₀ hcommonDown
      calc
        _ = (n + α) * (n + α + β) *
            (shiftedJacobi (n - 1) α β).coeff 0 := by ring
        _ = _ := hdown
        _ = (n * (shiftedJacobi n α β).coeff 0) *
            (n + α + β) := by ring
    have hup' :
        (shiftedJacobi (n + 1) α β).coeff 0 =
          ((n + α + 1) * (shiftedJacobi n α β).coeff 0) / (n + 1) :=
      (eq_div_iff hn1).2 (by simpa [mul_comm] using hupCancel)
    have hdown' :
        (shiftedJacobi (n - 1) α β).coeff 0 =
          (n * (shiftedJacobi n α β).coeff 0) / (n + α) :=
      (eq_div_iff hna).2 (by simpa [mul_comm] using hdownCancel)
    rw [hup', hdown']
    field_simp [hn1, hna]
    ring
  · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    by_cases hkle : k ≤ n
    · have hup := coeff_shiftedJacobi_succ_degree n k α β hkle
      have hwithin := coeff_succ_relation n (k - 1) α β (by lia)
      have hdu : ((n + 1 - k : ℕ) : ℝ) * (n + α + β + 1) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt (by lia : k < n + 1)))
        · have : 0 < (n : ℝ) + α + β + 1 := by
            have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          exact this.ne'
      have hdw : ((n - k + 1 : ℕ) : ℝ) * (n + α + β + k) ≠ 0 := by
        apply mul_ne_zero
        · positivity
        · have : 0 < (n : ℝ) + α + β + k := by
            have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
            have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
            linarith
          exact this.ne'
      have hup' :
          (shiftedJacobi (n + 1) α β).coeff k =
            ((n + α + 1) * (n + α + β + k + 1) *
              (shiftedJacobi n α β).coeff k) /
                (((n + 1 - k : ℕ) : ℝ) * (n + α + β + 1)) := by
        apply (eq_div_iff hdu).2
        calc
          _ = (((n + 1 - k : ℕ) : ℝ) * (n + α + β + 1)) *
              (shiftedJacobi (n + 1) α β).coeff k := by ring
          _ = _ := hup
      have hwithin' :
          (shiftedJacobi n α β).coeff (k - 1) =
            (-(k * (k + α)) * (shiftedJacobi n α β).coeff k) /
              (((n - k + 1 : ℕ) : ℝ) * (n + α + β + k)) := by
        apply (eq_div_iff hdw).2
        rw [Nat.sub_add_cancel hkpos] at hwithin
        norm_num only [Nat.cast_sub hkpos] at hwithin ⊢
        have hkpred : (k : ℝ) - 1 + α + 1 = k + α := by ring
        have hnsub : n - (k - 1) = n - k + 1 := by lia
        rw [hkpred, hnsub] at hwithin
        nlinarith [hwithin]
      have hcoeffX :
          (X * shiftedJacobi n α β).coeff k =
            (shiftedJacobi n α β).coeff (k - 1) := by
        rw [show k = k - 1 + 1 by lia, coeff_X_mul]
        rw [Nat.add_sub_cancel]
      rw [hcoeffX, hup', hwithin']
      have hcastUp : ((n + 1 - k : ℕ) : ℝ) = n + 1 - k := by
        rw [Nat.cast_sub (by lia)]
        push_cast
        rfl
      have hcastWithin : ((n - k + 1 : ℕ) : ℝ) = n - k + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hkle]
        push_cast
        rfl
      rw [hcastUp, hcastWithin]
      by_cases hklt : k < n
      · have hdown := coeff_shiftedJacobi_pred_degree n k α β (by lia) hklt
        have hdd : (n + α) * (n + α + β + k) ≠ 0 := by
          apply mul_ne_zero
          · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
            linarith
          · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
            have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
            linarith
        have hdown' :
            (shiftedJacobi (n - 1) α β).coeff k =
              (((n - k : ℕ) : ℝ) * (n + α + β) *
                (shiftedJacobi n α β).coeff k) /
                  ((n + α) * (n + α + β + k)) := by
          apply (eq_div_iff hdd).2
          calc
            _ = ((n + α) * (n + α + β + k)) *
                (shiftedJacobi (n - 1) α β).coeff k := by ring
            _ = _ := hdown
        rw [hdown']
        have hcastDown : ((n - k : ℕ) : ℝ) = n - k := by
          rw [Nat.cast_sub hkle]
        rw [hcastDown]
        have hu1 : (n + 1 - k : ℝ) ≠ 0 := by
          have hnR : (n : ℝ) > k := by exact_mod_cast hklt
          linarith
        have hu2 : (n + α + β + 1 : ℝ) ≠ 0 := by
          have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hw1 : (n - k + 1 : ℝ) ≠ 0 := by
          have hnR : (n : ℝ) > k := by exact_mod_cast hklt
          linarith
        have hw2 : (n + α + β + k : ℝ) ≠ 0 := by
          have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
          have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
          linarith
        have ha : (n + α : ℝ) ≠ 0 := by
          have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        field_simp [hu1, hu2, hw1, hw2, ha]
        ring
      · have hkn : k = n := by lia
        subst k
        have hpredzero : (shiftedJacobi (n - 1) α β).coeff n = 0 := by
          rw [coeff_shiftedJacobi, if_neg (by lia)]
        rw [hpredzero]
        simp only [mul_zero, sub_zero]
        have hupDen : (n + 1 - n : ℝ) = 1 := by ring
        have hwithinDen : (n - n + 1 : ℝ) = 1 := by ring
        have hwithinParam : (n + α + β + n : ℝ) = 2 * n + α + β := by ring
        rw [hupDen, hwithinDen, hwithinParam]
        simp only [one_mul]
        have hu2 : (n + α + β + 1 : ℝ) ≠ 0 := by
          have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hw2 : (2 * n + α + β : ℝ) ≠ 0 := by
          have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        field_simp [hu2, hw2]
        ring
    · by_cases hksucc : k = n + 1
      · subst k
        have hcoeffX :
            (X * shiftedJacobi n α β).coeff (n + 1) =
              (shiftedJacobi n α β).coeff n := by rw [coeff_X_mul]
        rw [hcoeffX]
        have hle_succ : n + 1 ≤ n + 1 := le_rfl
        have hle_self : n ≤ n := le_rfl
        have hnle : ¬n + 1 ≤ n := by lia
        have hnle_pred : ¬n + 1 ≤ n - 1 := by lia
        simp only [coeff_shiftedJacobi, if_pos hle_succ, if_pos hle_self,
          if_neg hnle, if_neg hnle_pred]
        simp only [Nat.sub_self, Ring.choose_zero_right, mul_one]
        have hlead := leading_choose_succ_degree n α β
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [pow_succ]
        linear_combination (-2 * (2 * n + α + β)) *
          ((-1 : ℝ) ^ n) * hlead
      · have hklarge : n + 1 < k := by lia
        have hcoeffX :
            (X * shiftedJacobi n α β).coeff k =
              (shiftedJacobi n α β).coeff (k - 1) := by
          rw [show k = k - 1 + 1 by lia, coeff_X_mul]
          rw [Nat.add_sub_cancel]
        rw [hcoeffX]
        have hkn : ¬k ≤ n := by lia
        have hknsucc : ¬k ≤ n + 1 := by lia
        have hkpredn : ¬k - 1 ≤ n := by lia
        have hknpred : ¬k ≤ n - 1 := by lia
        simp [coeff_shiftedJacobi, hkn, hknsucc, hkpredn, hknpred]

/-- The monic shifted Jacobi polynomials satisfy their standard Favard
recurrence from degree two onward. -/
theorem shiftedJacobiMonic_recurrence_of_two_le (n : ℕ) (α β : ℝ)
    (hn : 2 ≤ n) (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobiMonic (n + 1) α β =
      (X - C (shiftedJacobiDiag n α β)) * shiftedJacobiMonic n α β -
        C (shiftedJacobiSubdiag n α β) * shiftedJacobiMonic (n - 1) α β := by
  let d : ℝ := 2 * (n + 1) * (n + α + β + 1) * (2 * n + α + β)
  let u : ℝ := -2 * (2 * n + α + β + 2) * (2 * n + α + β + 1) *
    (2 * n + α + β)
  let v : ℝ := (2 * n + α + β + 1) *
    ((2 * n + α + β) * (2 * n + α + β + 2) - β ^ 2 + α ^ 2)
  let w : ℝ := 2 * (2 * n + α + β + 2) * (n + α) * (n + β)
  let lUp : ℝ := (-1 : ℝ) ^ (n + 1) *
    Ring.choose (((n + 1 : ℕ) : ℝ) + α + β + ((n + 1 : ℕ) : ℝ)) (n + 1)
  let l : ℝ := (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n
  let lDown : ℝ := (-1 : ℝ) ^ (n - 1) *
    Ring.choose (((n - 1 : ℕ) : ℝ) + α + β + ((n - 1 : ℕ) : ℝ)) (n - 1)
  let a : ℝ := (1 - (β ^ 2 - α ^ 2) /
    ((2 * n + α + β) * (2 * n + α + β + 2))) / 2
  let b : ℝ := n * (n + α) * (n + β) * (n + α + β) /
    ((2 * n + α + β) ^ 2 *
      (2 * n + α + β - 1) * (2 * n + α + β + 1))
  let t : ℝ := lUp⁻¹ / d
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : d ≠ 0 := by
    have hsum1 : 0 < (n + α + β + 1 : ℝ) := by linarith
    have hsum2 : 0 < (2 * n + α + β : ℝ) := by linarith
    dsimp [d]
    positivity
  have hlUp : lUp ≠ 0 := by
    dsimp [lUp]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        (leading_choose_pos (n + 1) hα hβ).ne')
  have hl : l ≠ 0 := by
    dsimp [l]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (leading_choose_pos n hα hβ).ne'
  have hlDown : lDown ≠ 0 := by
    dsimp [lDown]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (leading_choose_pos (n - 1) hα hβ).ne'
  have hleadUp :
      (n + 1) * (n + α + β + 1) * lUp =
        -(2 * n + α + β + 2) * (2 * n + α + β + 1) * l := by
    simpa [lUp, l] using leading_scale_succ_degree n α β
  have hleadDown :
      n * (n + α + β) * l =
        -(2 * n + α + β) * (2 * n + α + β - 1) * lDown := by
    have h := leading_scale_succ_degree (n - 1) α β
    simp only [Nat.sub_add_cancel (by lia : 1 ≤ n)] at h
    norm_num only [Nat.cast_sub (by lia : 1 ≤ n), Nat.cast_one] at h
    dsimp [l, lDown]
    have harg :
        (((n - 1 : ℕ) : ℝ) + α + β + ((n - 1 : ℕ) : ℝ)) =
          -2 + 2 * n + α + β := by
      rw [Nat.cast_sub (by lia : 1 ≤ n)]
      ring
    rw [harg]
    convert h using 1 <;> ring
  have hdu : d * lUp = u * l := by
    dsimp [d, u]
    linear_combination 2 * (2 * n + α + β) * hleadUp
  have hu : u ≠ 0 := by
    dsimp [u]
    have hE : (2 * n + α + β : ℝ) ≠ 0 := by linarith
    have hE1 : (2 * n + α + β + 1 : ℝ) ≠ 0 := by linarith
    have hE2 : (2 * n + α + β + 2 : ℝ) ≠ 0 := by linarith
    positivity
  have htU : t * u = l⁻¹ := by
    change lUp⁻¹ / d * u = l⁻¹
    calc
      _ = u / (d * lUp) := by
        field_simp [hlUp, hd]
      _ = u / (u * l) := by rw [hdu]
      _ = 1 / l := (div_eq_div_iff (mul_ne_zero hu hl) hl).2 (by ring)
      _ = l⁻¹ := by simp only [one_div]
  have hvu : v = -a * u := by
    dsimp [v, a, u]
    have hE : (2 * n + α + β : ℝ) ≠ 0 := by linarith
    have hE2 : (2 * n + α + β + 2 : ℝ) ≠ 0 := by linarith
    field_simp [hE, hE2]
    ring
  have htV : t * v = -(a * l⁻¹) := by
    rw [hvu, ← htU]
    ring
  have hwRelation : (-w) * lDown = -(b * u * l) := by
    dsimp only [b]
    have hE : (2 * n + α + β : ℝ) ≠ 0 := by linarith
    have hE1 : (2 * n + α + β - 1 : ℝ) ≠ 0 := by linarith
    have hE2 : (2 * n + α + β + 1 : ℝ) ≠ 0 := by linarith
    have hDen :
        (2 * n + α + β) ^ 2 * (2 * n + α + β - 1) *
            (2 * n + α + β + 1) ≠ 0 := by
      positivity
    rw [show
      -(n * (n + α) * (n + β) * (n + α + β) /
          ((2 * n + α + β) ^ 2 * (2 * n + α + β - 1) *
            (2 * n + α + β + 1)) * u * l) =
        (-(n * (n + α) * (n + β) * (n + α + β) * u * l)) /
          ((2 * n + α + β) ^ 2 * (2 * n + α + β - 1) *
            (2 * n + α + β + 1)) by ring]
    apply (eq_div_iff hDen).2
    dsimp [w, u]
    linear_combination
      (-2 * (2 * n + α + β + 2) * (2 * n + α + β + 1) *
        (2 * n + α + β) * (n + α) * (n + β)) * hleadDown
  have htW : t * (-w) = -(b * lDown⁻¹) := by
    change lUp⁻¹ / d * (-w) = -(b * lDown⁻¹)
    calc
      _ = (-w) / (d * lUp) := by
        field_simp [hlUp, hd]
      _ = (-w) / (u * l) := by rw [hdu]
      _ = (-b) / lDown :=
        (div_eq_div_iff (mul_ne_zero hu hl) hlDown).2 (by
          linear_combination hwRelation)
      _ = -(b * lDown⁻¹) := by rw [div_eq_mul_inv]; ring
  have hraw := shiftedJacobi_recurrence_raw n α β hn hα hβ
  change C d * shiftedJacobi (n + 1) α β =
    C u * (X * shiftedJacobi n α β) + C v * shiftedJacobi n α β -
      C w * shiftedJacobi (n - 1) α β at hraw
  simp only [shiftedJacobiMonic, shiftedJacobiDiag, shiftedJacobiSubdiag,
    if_neg (by lia : n ≠ 0), if_neg (by lia : n ≠ 1)]
  change C lUp⁻¹ * shiftedJacobi (n + 1) α β =
    (X - C a) * (C l⁻¹ * shiftedJacobi n α β) -
      C b * (C lDown⁻¹ * shiftedJacobi (n - 1) α β)
  have htD : t * d = lUp⁻¹ := by
    dsimp [t]
    field_simp [hd]
  calc
    _ = C t * (C d * shiftedJacobi (n + 1) α β) := by
      rw [← mul_assoc, ← C_mul, htD]
    _ = C t * (C u * (X * shiftedJacobi n α β) +
        C v * shiftedJacobi n α β - C w * shiftedJacobi (n - 1) α β) := by
      rw [hraw]
    _ = _ := by
      rw [mul_sub, mul_add]
      simp only [← mul_assoc, ← C_mul]
      rw [htU, htV]
      have htW' : t * w = b * lDown⁻¹ := by linarith [htW]
      rw [htW']
      simp only [map_neg, map_mul]
      ring

/-- The degree-one step of the monic shifted-Jacobi Favard recurrence. -/
theorem shiftedJacobiMonic_recurrence_one (α β : ℝ)
    (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobiMonic 2 α β =
      (X - C (shiftedJacobiDiag 1 α β)) * shiftedJacobiMonic 1 α β -
        C (shiftedJacobiSubdiag 1 α β) * shiftedJacobiMonic 0 α β := by
  have h2 : α + β + 2 ≠ 0 := by linarith
  have h3 : α + β + 3 ≠ 0 := by linarith
  have h4 : α + β + 4 ≠ 0 := by linarith
  let l2 : ℝ := (-1 : ℝ) ^ 2 * Ring.choose (2 + α + β + 2) 2
  have hl2 : l2 ≠ 0 := by
    dsimp [l2]
    exact mul_ne_zero (by norm_num) (leading_choose_pos 2 hα hβ).ne'
  have hl2eq : l2 = (α + β + 4) * (α + β + 3) / 2 := by
    dsimp [l2]
    rw [ring_choose_two]
    norm_num
    ring
  have hl2inv : l2⁻¹ = 2 / ((α + β + 4) * (α + β + 3)) := by
    rw [hl2eq]
    field_simp [h3, h4]
  have hraw0 :
      (shiftedJacobi 2 α β).coeff 0 = (α + 2) * (α + 1) / 2 := by
    rw [coeff_shiftedJacobi, if_pos (by lia : 0 ≤ 2)]
    rw [ring_choose_two]
    norm_num
    ring
  have hraw1 :
      (shiftedJacobi 2 α β).coeff 1 = -(α + 2) * (α + β + 3) := by
    rw [coeff_shiftedJacobi, if_pos (by lia : 1 ≤ 2)]
    norm_num [Ring.choose_one_right]
    ring
  have hraw2 :
      (shiftedJacobi 2 α β).coeff 2 = (α + β + 4) * (α + β + 3) / 2 := by
    rw [coeff_shiftedJacobi, if_pos (by lia : 2 ≤ 2)]
    rw [ring_choose_two]
    norm_num
    ring
  have hcoeff0 :
      (shiftedJacobiMonic 2 α β).coeff 0 =
        (α + 2) * (α + 1) / ((α + β + 4) * (α + β + 3)) := by
    rw [shiftedJacobiMonic, coeff_C_mul, hraw0]
    change l2⁻¹ * ((α + 2) * (α + 1) / 2) = _
    rw [hl2inv]
    field_simp [h3, h4]
  have hcoeff1 :
      (shiftedJacobiMonic 2 α β).coeff 1 =
        -(2 * (α + 2) / (α + β + 4)) := by
    rw [shiftedJacobiMonic, coeff_C_mul, hraw1]
    change l2⁻¹ * (-(α + 2) * (α + β + 3)) = _
    rw [hl2inv]
    field_simp [h3, h4]
  have hcoeff2 : (shiftedJacobiMonic 2 α β).coeff 2 = 1 := by
    rw [shiftedJacobiMonic, coeff_C_mul, hraw2]
    change l2⁻¹ * ((α + β + 4) * (α + β + 3) / 2) = 1
    rw [hl2inv]
    field_simp [h3, h4]
  have hpoly :
      shiftedJacobiMonic 2 α β =
        X ^ 2 - C (2 * (α + 2) / (α + β + 4)) * X +
          C ((α + 2) * (α + 1) / ((α + β + 4) * (α + β + 3))) := by
    ext k
    rcases lt_trichotomy k 2 with hk | rfl | hk
    · interval_cases k
      · simpa using hcoeff0
      · simpa using hcoeff1
    · simpa using hcoeff2
    · have hk3 : 3 ≤ k := by lia
      simp [coeff_shiftedJacobiMonic, Nat.not_le.mpr (by lia : 2 < k),
        show k ≠ 2 by lia, show 1 ≠ k by lia, show k ≠ 0 by lia,
        Polynomial.coeff_X, Polynomial.coeff_C]
  have hdiag :
      shiftedJacobiDiag 1 α β + (α + 1) / (α + β + 2) =
        2 * (α + 2) / (α + β + 4) := by
    have hdiag' :
        (1 - (β ^ 2 - α ^ 2) /
            ((α + β + 2) * (α + β + 4))) / 2 +
            (α + 1) / (α + β + 2) =
          2 * (α + 2) / (α + β + 4) := by
      field_simp [h2, h4]
      ring
    rw [shiftedJacobiDiag, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    convert hdiag' using 1 ; ring
  have hconst :
      shiftedJacobiDiag 1 α β * ((α + 1) / (α + β + 2)) -
          shiftedJacobiSubdiag 1 α β =
        (α + 2) * (α + 1) / ((α + β + 4) * (α + β + 3)) := by
    rw [show shiftedJacobiDiag 1 α β =
      2 * (α + 2) / (α + β + 4) - (α + 1) / (α + β + 2) by
        linarith [hdiag]]
    rw [shiftedJacobiSubdiag, if_neg (by norm_num : (1 : ℕ) ≠ 0), if_pos rfl]
    change
      (2 * (α + 2) / (α + β + 4) - (α + 1) / (α + β + 2)) *
            ((α + 1) / (α + β + 2)) -
          (1 + α) * (1 + β) / ((α + β + 2) ^ 2 * (α + β + 3)) =
        (α + 2) * (α + 1) / ((α + β + 4) * (α + β + 3))
    field_simp [h2, h3, h4]
    ring
  rw [hpoly, shiftedJacobiMonic_one α β h2, shiftedJacobiMonic_zero]
  simp only [mul_one]
  rw [show
    (X - C (shiftedJacobiDiag 1 α β)) * (X - C ((α + 1) / (α + β + 2))) -
        C (shiftedJacobiSubdiag 1 α β) =
      X ^ 2 - C (shiftedJacobiDiag 1 α β + (α + 1) / (α + β + 2)) * X +
        C (shiftedJacobiDiag 1 α β * ((α + 1) / (α + β + 2)) -
          shiftedJacobiSubdiag 1 α β) by
    simp only [map_add, map_sub, map_mul]
    ring]
  rw [hdiag, hconst]

/-- The monic shifted Jacobi polynomials satisfy their standard Favard
recurrence in every positive degree. -/
theorem shiftedJacobiMonic_recurrence (n : ℕ) (α β : ℝ)
    (hn : 1 ≤ n) (hα : -1 < α) (hβ : -1 < β) :
    shiftedJacobiMonic (n + 1) α β =
      (X - C (shiftedJacobiDiag n α β)) * shiftedJacobiMonic n α β -
        C (shiftedJacobiSubdiag n α β) * shiftedJacobiMonic (n - 1) α β := by
  by_cases hn1 : n = 1
  · subst n
    exact shiftedJacobiMonic_recurrence_one α β hα hβ
  · exact shiftedJacobiMonic_recurrence_of_two_le n α β (by lia) hα hβ

/-- The subdiagonal coefficient in the monic shifted-Jacobi recurrence is
strictly positive in every positive degree when both parameters exceed
`-1`. -/
theorem shiftedJacobiSubdiag_pos (n : ℕ) {α β : ℝ}
    (hn : 1 ≤ n) (hα : -1 < α) (hβ : -1 < β) :
    0 < shiftedJacobiSubdiag n α β := by
  by_cases hn1 : n = 1
  · subst n
    rw [shiftedJacobiSubdiag, if_neg (by norm_num : (1 : ℕ) ≠ 0), if_pos rfl]
    have hα1 : 0 < 1 + α := by linarith
    have hβ1 : 0 < 1 + β := by linarith
    have hsum2 : 0 < α + β + 2 := by linarith
    have hsum3 : 0 < α + β + 3 := by linarith
    positivity
  · rw [shiftedJacobiSubdiag, if_neg (by lia), if_neg hn1]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (by lia : 2 ≤ n)
    have hnα : 0 < (n : ℝ) + α := by linarith
    have hnβ : 0 < (n : ℝ) + β := by linarith
    have hnαβ : 0 < (n : ℝ) + α + β := by linarith
    have htwo : 0 < 2 * (n : ℝ) + α + β := by linarith
    have htwoPred : 0 < 2 * (n : ℝ) + α + β - 1 := by linarith
    have htwoSucc : 0 < 2 * (n : ℝ) + α + β + 1 := by linarith
    positivity

end Polynomial
