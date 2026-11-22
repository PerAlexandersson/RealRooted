module

public import RealRooted.Hermite.Homogeneous
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Derivatives of quadratic exponentials

The homogeneous Hermite normalization is the exponential generating function
`exp (x z + s z²)`. In particular, `s = -1` and `x = 2 X` give the
physicists' Hermite polynomials used by O'Sullivan.
-/

public section

open Polynomial Complex

namespace RealRooted

private theorem hasDerivAt_hermiteHomogeneous_affine (x s z : ℂ) (n : ℕ) :
    HasDerivAt (fun w => hermiteHomogeneous (x + 2 * s * w) s (n + 1))
      ((n + 1 : ℂ) * hermiteHomogeneous (x + 2 * s * z) s n * (2 * s)) z := by
  have h := ((hermiteHomogeneousPoly s (n + 1)).hasDerivAt (x + 2 * s * z)).comp z
    (((hasDerivAt_id z).const_mul (2 * s)).const_add x)
  rw [derivative_hermiteHomogeneousPoly] at h
  simpa only [Function.comp_def, hermiteHomogeneousPoly, eval_hermiteHomogeneous,
    eval_mul, eval_natCast, Nat.cast_add, Nat.cast_one, eval_add, eval_one,
    id_eq, mul_one] using h

/-- Iterated derivatives of a quadratic exponential are homogeneous Hermite polynomials. -/
theorem iteratedDeriv_exp_quadratic (x s : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => exp (x * w + s * w ^ 2)) z =
      hermiteHomogeneous (x + 2 * s * z) s n * exp (x * z + s * z ^ 2) := by
  have he (z : ℂ) : HasDerivAt (fun w : ℂ => exp (x * w + s * w ^ 2))
      ((x + 2 * s * z) * exp (x * z + s * z ^ 2)) z := by
    convert (((hasDerivAt_id' z).const_mul x).add
      ((hasDerivAt_pow 2 z).const_mul s)).cexp using 1
    dsimp
    ring
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    cases n with
    | zero => simpa using (he z).deriv
    | succ n =>
      rw [((hasDerivAt_hermiteHomogeneous_affine x s z n).fun_mul (he z)).deriv,
        hermiteHomogeneous_add_two]
      push_cast
      ring

/-- The homogeneous Hermite polynomial is the Taylor data of a quadratic exponential. -/
theorem iteratedDeriv_exp_quadratic_zero (x s : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ => exp (x * w + s * w ^ 2)) 0 =
      hermiteHomogeneous x s n := by
  simp [iteratedDeriv_exp_quadratic]

end RealRooted
