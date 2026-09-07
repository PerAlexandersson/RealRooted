/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Hermite

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Probabilists' Hermite polynomials over the reals

This file maps Mathlib's canonical probabilists' Hermite polynomials from
`ℤ[X]` to `ℝ[X]`.  The normalization is

`H₀ = 1`, `H₁ = X`, and `Hₙ₊₂ = X Hₙ₊₁ - (n + 1) Hₙ`.

This family is unrelated to the positive-recurrence reverse-Hermite basis in
`RealRooted.Transforms.ReverseHermite`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Mathlib's canonical probabilists' Hermite polynomial, mapped to `ℝ[X]`. -/
abbrev hermiteReal (n : ℕ) : ℝ[X] :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp] theorem coeff_hermiteReal (n k : ℕ) :
    (hermiteReal n).coeff k = ((Polynomial.hermite n).coeff k : ℝ) := by
  simp [hermiteReal]

@[simp] theorem hermiteReal_zero : hermiteReal 0 = 1 := by
  simp [hermiteReal]

@[simp] theorem hermiteReal_one : hermiteReal 1 = X := by
  simp [hermiteReal]

/-- Differentiating lowers the index of the real Hermite family. -/
@[simp] theorem derivative_hermiteReal_succ (n : ℕ) :
    (hermiteReal (n + 1)).derivative = C (n + 1 : ℝ) * hermiteReal n := by
  rw [show hermiteReal (n + 1) =
    (Polynomial.hermite (n + 1)).map (Int.castRingHom ℝ) by rfl]
  rw [Polynomial.derivative_map, Polynomial.derivative_hermite_succ]
  simp [hermiteReal]

/-- The real probabilists' Hermite family satisfies its monic three-term
recurrence. -/
theorem hermiteReal_add_two (n : ℕ) :
    hermiteReal (n + 2) =
      X * hermiteReal (n + 1) - C (n + 1 : ℝ) * hermiteReal n := by
  simpa [hermiteReal] using
    congrArg (fun p : ℤ[X] => p.map (Int.castRingHom ℝ))
      (Polynomial.hermite_add_two n)

/-- Evaluation after mapping to `ℝ` agrees with algebraic evaluation of
Mathlib's integer-coefficient polynomial. -/
@[simp] theorem eval_hermiteReal (n : ℕ) (x : ℝ) :
    (hermiteReal n).eval x = aeval x (Polynomial.hermite n) := by
  simpa [hermiteReal] using
    Polynomial.eval_map_algebraMap (B := ℝ) (Polynomial.hermite n) x

@[simp] theorem hermiteReal_two :
    hermiteReal 2 = X ^ 2 - 1 := by
  rw [show 2 = 0 + 2 by rfl, hermiteReal_add_two]
  simp [pow_two]

@[simp] theorem hermiteReal_three :
    hermiteReal 3 = X ^ 3 - C 3 * X := by
  rw [show 3 = 1 + 2 by rfl, hermiteReal_add_two]
  rw [hermiteReal_two, hermiteReal_one]
  rw [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]
  rw [Polynomial.C_ofNat (R := ℝ) 2, Polynomial.C_ofNat (R := ℝ) 3]
  ring

end RealRooted
