/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer

import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A duplication identity for descending Pochhammer polynomials

This Mathlib-shaped shim records an algebraic evaluation identity used by a
later half-integer convolution calculation.  It does not assert that
calculation, or any root-preservation consequence.
-/

@[expose] public section

open Polynomial

namespace Polynomial

noncomputable section

/-- The ratio of descending Pochhammer evaluations that occurs in generalized
rectangular convolution kernels. -/
def descPochhammerRatio {R : Type*} [Field R] (x : R) (i j : ℕ) : R :=
  (descPochhammer R (i + j)).eval x /
    ((descPochhammer R i).eval x * (descPochhammer R j).eval x)

/-- Evaluating a descending Pochhammer polynomial at twice an argument factors
into the two adjacent half-shifted descending Pochhammer evaluations. -/
theorem descPochhammer_eval_two_mul {R : Type*} [Field R] [CharZero R]
    (k : ℕ) (x : R) :
    (descPochhammer R (2 * k)).eval (2 * x) =
      (4 : R) ^ k * (descPochhammer R k).eval x *
        (descPochhammer R k).eval (x - 1 / 2) := by
  induction k with
  | zero => norm_num [descPochhammer_zero]
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by lia]
      rw [descPochhammer_succ_eval, descPochhammer_succ_eval, ih]
      rw [pow_succ, descPochhammer_succ_eval, descPochhammer_succ_eval]
      push_cast
      ring

/-- The descending-Pochhammer ratio at doubled parameters factors into its
two adjacent half-shifted ratios. -/
theorem descPochhammerRatio_two_mul {R : Type*} [Field R] [CharZero R]
    (x : R) (i j : ℕ) :
    descPochhammerRatio (2 * x) (2 * i) (2 * j) =
      descPochhammerRatio x i j * descPochhammerRatio (x - 1 / 2) i j := by
  unfold descPochhammerRatio
  rw [show 2 * i + 2 * j = 2 * (i + j) by lia]
  have hdup (r : ℕ) :
      (descPochhammer R (2 * r)).eval (2 * x) =
        (4 : R) ^ r * (descPochhammer R r).eval x *
          (descPochhammer R r).eval (x - 1 / 2) := by
    exact descPochhammer_eval_two_mul r x
  let a := (descPochhammer R (i + j)).eval x
  let b := (descPochhammer R (i + j)).eval (x - 1 / 2)
  let ai := (descPochhammer R i).eval x
  let bi := (descPochhammer R i).eval (x - 1 / 2)
  let aj := (descPochhammer R j).eval x
  let bj := (descPochhammer R j).eval (x - 1 / 2)
  rw [hdup (i + j), hdup i, hdup j, pow_add]
  change ((4 : R) ^ i * 4 ^ j * a * b) /
      (((4 : R) ^ i * ai * bi) * (4 ^ j * aj * bj)) =
    a / (ai * aj) * (b / (bi * bj))
  have hfour : (4 : R) ^ i * 4 ^ j ≠ 0 := by
    apply mul_ne_zero <;> apply pow_ne_zero <;> norm_num
  calc
    _ = ((4 : R) ^ i * 4 ^ j * (a * b)) /
        ((4 : R) ^ i * 4 ^ j * ((ai * bi) * (aj * bj))) := by ring
    _ = (a * b) / ((ai * bi) * (aj * bj)) :=
      mul_div_mul_left _ _ hfour
    _ = _ := by
      rw [← mul_div_mul_comm]
      congr 1
      ring

end

end Polynomial
