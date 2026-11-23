/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic

/-!
# Derivative polynomials for the xi Fourier kernel

The derivative of a summand of the Fourier kernel replaces `p` by
`4 X p' + (5 - 4 X) p`. The indexing here starts with derivative order zero;
Csordas and Varga (1988), Section 3, index the same polynomials from one.
-/

public section

open Polynomial
open scoped Polynomial

/-- The polynomial in the derivative of order `n` of a xi Fourier-kernel summand. -/
@[expose] noncomputable def riemannXiFourierPolynomial : ℕ → ℝ[X]
  | 0 => 2 * X - 3
  | n + 1 => 4 * X * (riemannXiFourierPolynomial n).derivative +
      (5 - 4 * X) * riemannXiFourierPolynomial n

/-- The recurrence for the Fourier-kernel derivative polynomials. -/
theorem riemannXiFourierPolynomial_succ (n : ℕ) :
    riemannXiFourierPolynomial (n + 1) =
      4 * X * (riemannXiFourierPolynomial n).derivative +
        (5 - 4 * X) * riemannXiFourierPolynomial n := rfl

/-- The explicit derivative polynomial of order `0`. -/
theorem riemannXiFourierPolynomial_zero :
    riemannXiFourierPolynomial 0 = 2 * X - 3 := by
  rfl

/-- The explicit derivative polynomial of order `1`. -/
theorem riemannXiFourierPolynomial_one :
    riemannXiFourierPolynomial 1 = -8 * X ^ 2 + 30 * X - 15 := by
  norm_num [riemannXiFourierPolynomial, Polynomial.derivative_X_pow]
  ring

/-- The explicit derivative polynomial of order `2`. -/
theorem riemannXiFourierPolynomial_two :
    riemannXiFourierPolynomial 2 = 32 * X ^ 3 - 224 * X ^ 2 + 330 * X - 75 := by
  norm_num [riemannXiFourierPolynomial, Polynomial.derivative_X_pow]
  ring

/-- The explicit derivative polynomial of order `3`. -/
theorem riemannXiFourierPolynomial_three :
    riemannXiFourierPolynomial 3 = -128 * X ^ 4 + 1440 * X ^ 3 - 4232 * X ^ 2 + 3270 * X - 375 := by
  norm_num [riemannXiFourierPolynomial, Polynomial.derivative_X_pow]
  ring

/-- The explicit derivative polynomial of order `4`. -/
theorem riemannXiFourierPolynomial_four :
    riemannXiFourierPolynomial 4 = 512 * X ^ 5 - 8448 * X ^ 4 + 41408 * X ^ 3 - 68096 * X ^ 2 +
    30930 * X - 1875 := by
  norm_num [riemannXiFourierPolynomial, Polynomial.derivative_X_pow]
  ring

/-- The explicit derivative polynomial of order `5`. -/
theorem riemannXiFourierPolynomial_five :
    riemannXiFourierPolynomial 5 = -2048 * X ^ 6 + 46592 * X ^ 5 - 343040 * X ^ 4 + 976320 * X
    ^ 3 - 1008968 * X ^ 2 + 285870 * X - 9375 := by
  norm_num [riemannXiFourierPolynomial, Polynomial.derivative_X_pow]
  ring

/-- The explicit derivative polynomial of order `6`. -/
theorem riemannXiFourierPolynomial_six :
    riemannXiFourierPolynomial 6 = 8192 * X ^ 7 - 245760 * X ^ 6 + 2536960 * X ^ 5 - 11109120 *
    X ^ 4 + 20633312 * X ^ 3 - 14260064 * X ^ 2 + 2610330 * X - 46875 := by
  norm_num [riemannXiFourierPolynomial, Polynomial.derivative_X_pow]
  ring
