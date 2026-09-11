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

end Polynomial
