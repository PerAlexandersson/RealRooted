/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import Mathlib.Tactic.Ring

/-!
# Additional algebraic identities for Hermite polynomials

This file extends Mathlib's canonical probabilists' Hermite polynomials with
the lowering identity and the equivalent three-term recurrence.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Polynomial

/-- Differentiating the next probabilists' Hermite polynomial lowers its
index. -/
@[simp] theorem derivative_hermite_succ (n : ℕ) :
    (hermite (n + 1)).derivative = C (n + 1 : ℤ) * hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hermite_succ, derivative_sub, derivative_mul, derivative_X,
        one_mul, ih, derivative_C_mul]
      calc
        hermite (n + 1) + X * (C (n + 1 : ℤ) * hermite n) -
            C (n + 1 : ℤ) * derivative (hermite n) =
          hermite (n + 1) +
            C (n + 1 : ℤ) * (X * hermite n - derivative (hermite n)) := by
              ring
        _ = hermite (n + 1) + C (n + 1 : ℤ) * hermite (n + 1) := by
          rw [← hermite_succ]
        _ = (C 1 + C (n + 1 : ℤ)) * hermite (n + 1) := by
          simp [add_mul]
        _ = C (n + 2 : ℤ) * hermite (n + 1) := by
          rw [← C_add]
          congr 2
          ring

/-- The probabilists' Hermite polynomials satisfy their monic three-term
recurrence. -/
theorem hermite_add_two (n : ℕ) :
    hermite (n + 2) =
      X * hermite (n + 1) - C (n + 1 : ℤ) * hermite n := by
  rw [hermite_succ, derivative_hermite_succ]

end Polynomial
