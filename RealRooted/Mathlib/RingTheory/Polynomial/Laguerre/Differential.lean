/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Differential identities for generalized Laguerre polynomials

The identities in this file use the monic sign-reversed normalization
`generalizedLaguerre n α = n! L_n^(α)(-X)`.
-/

@[expose] public section

namespace Polynomial

universe u

variable {R : Type u} [CommSemiring R]

/-- The first-order raising operator for the sign-reversed Laguerre family. -/
noncomputable def laguerreRaisingStep (r : R) (p : R[X]) : R[X] :=
  (X + C r) * p + X * p.derivative

/-- Coefficients of the first-order Laguerre raising step. -/
theorem coeff_laguerreRaisingStep (r : R) (p : R[X]) (k : ℕ) :
    (laguerreRaisingStep r p).coeff k =
      (if k = 0 then 0 else p.coeff (k - 1)) +
        (r + k) * p.coeff k := by
  have hform : laguerreRaisingStep r p =
      X * p + C r * p + X * p.derivative := by
    simp [laguerreRaisingStep]
    ring
  rw [hform]
  cases k with
  | zero => simp [coeff_add, coeff_derivative]
  | succ k =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul,
        coeff_derivative, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring_nf

/-- Adjacent coefficients satisfy the Laguerre differential ratio without
division. -/
theorem succ_mul_mul_coeff_generalizedLaguerre
    (n k : ℕ) (α : R) (hk : k < n) :
    (k + 1 : R) * (α + k + 1) *
        (generalizedLaguerre n α).coeff (k + 1) =
      (n - k : ℕ) * (generalizedLaguerre n α).coeff k := by
  rw [coeff_generalizedLaguerre,
    if_pos (Nat.succ_le_iff.mpr hk), coeff_generalizedLaguerre,
    if_pos hk.le]
  have hpoch :
      (ascPochhammer R (n - k)).eval (α + k + 1) =
        (α + k + 1) *
          (ascPochhammer R (n - (k + 1))).eval (α + (k + 1) + 1) := by
    rw [show n - k = (n - (k + 1)) + 1 by lia,
      ascPochhammer_succ_left]
    simp [eval_mul, eval_comp]
    ring_nf
  have hchoose := congrArg (Nat.castRingHom R)
    (Nat.choose_succ_right_eq n k)
  change (((n.choose (k + 1)) * (k + 1) : ℕ) : R) =
    ((n.choose k * (n - k) : ℕ) : R) at hchoose
  push_cast at hchoose
  norm_num only [Nat.cast_add, Nat.cast_one] at hchoose hpoch ⊢
  rw [hpoch]
  calc
    ((k : R) + 1) * (α + k + 1) *
        ((n.choose (k + 1) : R) *
          (ascPochhammer R (n - (k + 1))).eval (α + ((k : R) + 1) + 1)) =
      ((n.choose (k + 1) : R) * ((k : R) + 1)) *
        ((α + k + 1) *
          (ascPochhammer R (n - (k + 1))).eval
            (α + ((k : R) + 1) + 1)) := by
        ring
    _ = ((n.choose k : R) * (n - k : ℕ)) *
        ((α + k + 1) *
          (ascPochhammer R (n - (k + 1))).eval
            (α + ((k : R) + 1) + 1)) := by
        rw [hchoose]
    _ = (n - k : ℕ) * ((n.choose k : R) *
        ((α + k + 1) *
          (ascPochhammer R (n - (k + 1))).eval
            (α + ((k : R) + 1) + 1))) := by
      ring_nf

/-- Coefficient form of the generalized Laguerre differential equation. -/
theorem generalizedLaguerre_differential_coeff
    (n k : ℕ) (α : R) :
    (k + 1 : R) * (α + k + 1) *
        (generalizedLaguerre n α).coeff (k + 1) +
      k * (generalizedLaguerre n α).coeff k =
        n * (generalizedLaguerre n α).coeff k := by
  by_cases hk : k < n
  · rw [succ_mul_mul_coeff_generalizedLaguerre n k α hk,
      ← add_mul, ← Nat.cast_add, Nat.sub_add_cancel hk.le]
  · by_cases hkn : k = n
    · subst k
      rw [coeff_generalizedLaguerre,
        if_neg (by lia : ¬n + 1 ≤ n)]
      simp
    · have hnk : n < k := lt_of_le_of_ne (Nat.le_of_not_gt hk) (Ne.symm hkn)
      rw [coeff_generalizedLaguerre,
        if_neg (Nat.not_le.mpr (hnk.trans (Nat.lt_succ_self k))),
        coeff_generalizedLaguerre, if_neg (Nat.not_le.mpr hnk)]
      simp

/-- The Laguerre differential operator in the sign-reversed normalization. -/
noncomputable def laguerreDifferentialOperator (α : R) (p : R[X]) : R[X] :=
  X * p.derivative.derivative + (C (α + 1) + X) * p.derivative

@[simp] theorem laguerreDifferentialOperator_zero (α : R) :
    laguerreDifferentialOperator α 0 = 0 := by
  simp [laguerreDifferentialOperator]

/-- The Laguerre differential operator is additive. -/
theorem laguerreDifferentialOperator_add (α : R) (p q : R[X]) :
    laguerreDifferentialOperator α (p + q) =
      laguerreDifferentialOperator α p + laguerreDifferentialOperator α q := by
  simp only [laguerreDifferentialOperator, derivative_add]
  ring_nf

/-- The Laguerre differential operator commutes with scalar multiplication. -/
theorem laguerreDifferentialOperator_C_mul (α a : R) (p : R[X]) :
    laguerreDifferentialOperator α (C a * p) =
      C a * laguerreDifferentialOperator α p := by
  simp only [laguerreDifferentialOperator, derivative_mul, derivative_C,
    zero_mul, zero_add]
  ring

/-- The Laguerre differential operator is triangular in the monomial basis. -/
theorem laguerreDifferentialOperator_X_pow (α : R) (n : ℕ) :
    laguerreDifferentialOperator α (X ^ n) =
      C ((n : R) * ((n : R) + α)) * X ^ (n - 1) +
        C (n : R) * X ^ n := by
  cases n with
  | zero => simp [laguerreDifferentialOperator]
  | succ n =>
      rw [laguerreDifferentialOperator, derivative_X_pow_succ,
        derivative_mul, derivative_C, zero_mul, zero_add]
      cases n with
      | zero => simp; ring
      | succ n =>
          rw [derivative_X_pow_succ]
          push_cast
          simp only [map_add, map_mul, map_one]
          ring

/-- The Laguerre differential operator on a coefficient-weighted monomial. -/
theorem laguerreDifferentialOperator_monomial (α a : R) (n : ℕ) :
    laguerreDifferentialOperator α (monomial n a) =
      monomial (n - 1) (a * n * (n + α)) + monomial n (a * n) := by
  rw [← C_mul_X_pow_eq_monomial,
    laguerreDifferentialOperator_C_mul,
    laguerreDifferentialOperator_X_pow]
  simp only [← C_mul_X_pow_eq_monomial]
  simp only [map_mul]
  ring

/-- Coefficients of the Laguerre differential operator. -/
theorem coeff_laguerreDifferentialOperator (α : R) (p : R[X]) (k : ℕ) :
    (laguerreDifferentialOperator α p).coeff k =
      (k + 1 : R) * (α + k + 1) * p.coeff (k + 1) +
        k * p.coeff k := by
  have hform : laguerreDifferentialOperator α p =
      C (α + 1) * p.derivative + X * p.derivative +
        X * p.derivative.derivative := by
    simp [laguerreDifferentialOperator]
    ring
  rw [hform]
  cases k with
  | zero =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero,
        coeff_derivative, Nat.zero_add, Nat.cast_zero, zero_mul, add_zero]
      ring
  | succ k =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul,
        coeff_derivative]
      push_cast
      ring

/-- The generalized Laguerre differential equation. -/
theorem generalizedLaguerre_ode (n : ℕ) (α : R) :
    laguerreDifferentialOperator α (generalizedLaguerre n α) =
      C (n : R) * generalizedLaguerre n α := by
  ext k
  rw [coeff_laguerreDifferentialOperator, coeff_C_mul]
  exact generalizedLaguerre_differential_coeff n k α

/-- The first-order raising recurrence for generalized Laguerre polynomials. -/
theorem generalizedLaguerre_succ (n : ℕ) (α : R) :
    generalizedLaguerre (n + 1) α =
      laguerreRaisingStep ((n : R) + α + 1) (generalizedLaguerre n α) := by
  ext j
  rw [coeff_laguerreRaisingStep]
  cases j with
  | zero =>
      rw [coeff_generalizedLaguerre, if_pos (Nat.zero_le _),
        coeff_generalizedLaguerre, if_pos (Nat.zero_le _)]
      simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero,
        one_mul, Nat.cast_zero, add_zero]
      rw [ascPochhammer_succ_eval]
      push_cast
      simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero,
        one_mul]
      ring_nf
  | succ k =>
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rcases lt_trichotomy k n with hk | rfl | hk
      · have hpred :
          (ascPochhammer R (n - k)).eval (α + k + 1) =
            (α + k + 1) *
              (ascPochhammer R (n - (k + 1))).eval
                (α + (k + 1) + 1) := by
          rw [show n - k = (n - (k + 1)) + 1 by lia,
            ascPochhammer_succ_left]
          simp [eval_mul, eval_comp]
          ring_nf
        have htarget :
          (ascPochhammer R (n - k)).eval (α + (k + 1) + 1) =
            (ascPochhammer R (n - (k + 1))).eval
                (α + (k + 1) + 1) * ((n : R) + α + 1) := by
          rw [show n - k = (n - (k + 1)) + 1 by lia,
            ascPochhammer_succ_eval]
          have hsub := congrArg (Nat.castRingHom R)
            (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hk))
          push_cast at hsub
          have hsum :
              α + ((k : R) + 1) + 1 + (n - (k + 1) : ℕ) =
                (n : R) + α + 1 := by
            calc
              α + ((k : R) + 1) + 1 + (n - (k + 1) : ℕ) =
                  α + 1 + ((n - (k + 1) : ℕ) + ((k : R) + 1)) := by ring
              _ = α + 1 + n := by rw [hsub]
              _ = (n : R) + α + 1 := by ring
          rw [hsum]
        have hchoose := congrArg (Nat.castRingHom R)
          (Nat.choose_succ_right_eq n k)
        change (((n.choose (k + 1)) * (k + 1) : ℕ) : R) =
          ((n.choose k * (n - k) : ℕ) : R) at hchoose
        push_cast at hchoose
        rw [coeff_generalizedLaguerre, if_pos (by lia : k + 1 ≤ n + 1),
          coeff_generalizedLaguerre, if_pos hk.le,
          coeff_generalizedLaguerre, if_pos (Nat.succ_le_iff.mpr hk)]
        rw [Nat.add_sub_add_right, Nat.choose_succ_succ, Nat.cast_add]
        norm_num only [Nat.cast_add, Nat.cast_one] at hchoose htarget hpred ⊢
        rw [htarget, hpred]
        have hsub := congrArg (Nat.castRingHom R)
          (Nat.sub_add_cancel hk.le)
        push_cast at hsub
        have hsplit :
            (n : R) + α + 1 = (n - k : ℕ) + (α + k + 1) := by
          rw [← hsub]
          ring
        let a : R := n.choose k
        let b : R := n.choose (k + 1)
        let e := (ascPochhammer R (n - (k + 1))).eval
          (α + ((k : R) + 1) + 1)
        change (a + b) * (e * ((n : R) + α + 1)) =
          a * ((α + k + 1) * e) +
            ((n : R) + α + 1 + ((k : R) + 1)) * (b * e)
        calc
          (a + b) * (e * ((n : R) + α + 1)) =
              e * ((a + b) * ((n : R) + α + 1)) := by ring
          _ = e * (a * (α + k + 1) +
              (((n : R) + α + 1) + ((k : R) + 1)) * b) := by
            congr 1
            calc
              (a + b) * ((n : R) + α + 1) =
                  (a + b) * ((n - k : ℕ) + (α + k + 1)) := by rw [hsplit]
              _ =
                  a * (n - k : ℕ) + a * (α + k + 1) +
                    b * ((n - k : ℕ) + (α + k + 1)) := by ring
              _ = b * ((k : R) + 1) + a * (α + k + 1) +
                    b * ((n - k : ℕ) + (α + k + 1)) := by rw [hchoose]
              _ = a * (α + k + 1) +
                    (((n - k : ℕ) + (α + k + 1)) +
                      ((k : R) + 1)) * b := by ring
              _ = a * (α + k + 1) +
                    (((n : R) + α + 1) + ((k : R) + 1)) * b := by rw [hsplit]
          _ = a * ((α + k + 1) * e) +
              ((n : R) + α + 1 + ((k : R) + 1)) * (b * e) := by ring
      · simp [coeff_generalizedLaguerre]
      · rw [coeff_generalizedLaguerre,
          if_neg (Nat.not_le.mpr (Nat.succ_lt_succ hk)),
          coeff_generalizedLaguerre, if_neg (Nat.not_le.mpr hk),
          coeff_generalizedLaguerre,
          if_neg (Nat.not_le.mpr (hk.trans k.lt_succ_self))]
        simp

/-- The second-derivative recurrence used by the generalized Laguerre
interlacing criterion. -/
theorem generalizedLaguerre_second_derivative_recurrence (n : ℕ) (α : R) :
    generalizedLaguerre (n + 1) α =
      (C (α + 1) + X) * generalizedLaguerre n α +
        (C (α + 1) + C 2 * X) *
          (generalizedLaguerre n α).derivative +
          X * (generalizedLaguerre n α).derivative.derivative := by
  rw [generalizedLaguerre_succ, laguerreRaisingStep]
  have hode := generalizedLaguerre_ode n α
  simp only [laguerreDifferentialOperator] at hode
  calc
    (X + C ((n : R) + α + 1)) * generalizedLaguerre n α +
        X * (generalizedLaguerre n α).derivative =
      (C (α + 1) + X) * generalizedLaguerre n α +
        X * (generalizedLaguerre n α).derivative +
          C (n : R) * generalizedLaguerre n α := by
            simp only [map_add, map_one]
            ring
    _ = (C (α + 1) + X) * generalizedLaguerre n α +
        X * (generalizedLaguerre n α).derivative +
          (X * (generalizedLaguerre n α).derivative.derivative +
            (C (α + 1) + X) *
              (generalizedLaguerre n α).derivative) := by rw [hode]
    _ = (C (α + 1) + X) * generalizedLaguerre n α +
        (C (α + 1) + C 2 * X) *
          (generalizedLaguerre n α).derivative +
          X * (generalizedLaguerre n α).derivative.derivative := by
            simp only [map_add, map_one, map_ofNat]
            ring

/-- Differentiation lowers the index and raises the parameter. -/
theorem derivative_generalizedLaguerre (n : ℕ) (α : R) :
    (generalizedLaguerre (n + 1) α).derivative =
      C (n + 1 : R) * generalizedLaguerre n (α + 1) := by
  ext k
  rw [coeff_derivative, coeff_C_mul]
  by_cases hk : k ≤ n
  · rw [coeff_generalizedLaguerre, if_pos (Nat.succ_le_succ hk),
      coeff_generalizedLaguerre, if_pos hk]
    rw [Nat.add_sub_add_right]
    have hchoose := congrArg (Nat.castRingHom R)
      (Nat.add_one_mul_choose_eq n k)
    change (((n + 1) * n.choose k : ℕ) : R) =
      (((n + 1).choose (k + 1) * (k + 1) : ℕ) : R) at hchoose
    push_cast at hchoose
    norm_num only [Nat.cast_add, Nat.cast_one] at hchoose ⊢
    have harg : α + ((k : R) + 1) + 1 = α + 1 + k + 1 := by ring
    rw [harg]
    let e := (ascPochhammer R (n - k)).eval (α + 1 + k + 1)
    calc
      ((n + 1).choose (k + 1) : R) * e * (k + 1) =
          ((n + 1).choose (k + 1) * (k + 1) : R) * e := by ring
      _ = ((n + 1 : R) * n.choose k) * e := by rw [← hchoose]
      _ = (n + 1 : R) * ((n.choose k : R) * e) := by ring
  · have hkn : n < k := Nat.lt_of_not_ge hk
    rw [coeff_generalizedLaguerre,
      if_neg (Nat.not_le.mpr (Nat.succ_lt_succ hkn)),
      coeff_generalizedLaguerre, if_neg hk]
    simp

end Polynomial
