/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Derivative identities for positive affine resolvents

The elementary derivative and Euler-step identities below are the algebraic
part of the two-index logarithmic-derivative hierarchy. They hold wherever
the denominator is nonzero; positivity is not needed for these identities.
-/

public section

open Filter Topology

namespace Real

/-- The derivative of a constant multiple of a positive natural reciprocal
power of an affine function. -/
theorem hasDerivAt_const_div_one_add_mul_pow (a b : ℝ) (q : ℕ)
    {x : ℝ} (hx : 1 + a * x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ b / (1 + a * y) ^ (q + 1))
      (-((q + 1 : ℕ) : ℝ) * a * b / (1 + a * x) ^ (q + 2)) x := by
  have hd : HasDerivAt (fun y : ℝ ↦ 1 + a * y) a x :=
    (hasDerivAt_const_mul a).const_add 1
  have h := (hasDerivAt_const x b).div (hd.pow (q + 1)) (pow_ne_zero _ hx)
  convert h using 1
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  field_simp [hx, pow_succ]
  ring

/-- Multiplication by the reciprocal exponent plus the Euler derivative
increases that exponent by one. This is the kernel cancellation underlying
Zhang's recurrence, equation (1.7). -/
theorem mul_const_div_add_mul_deriv_eq (a b : ℝ) (q : ℕ)
    {x : ℝ} (hx : 1 + a * x ≠ 0) :
    ((q + 1 : ℕ) : ℝ) * (b / (1 + a * x) ^ (q + 1)) +
        x * deriv (fun y : ℝ ↦ b / (1 + a * y) ^ (q + 1)) x =
      ((q + 1 : ℕ) : ℝ) * b / (1 + a * x) ^ (q + 2) := by
  rw [(hasDerivAt_const_div_one_add_mul_pow a b q hx).deriv]
  field_simp [hx, pow_succ]
  ring

/-- Every iterated derivative of a linear resolvent has its expected
factorial, slope power and alternating sign, away from its pole. -/
theorem iteratedDeriv_const_div_one_add_mul (a : ℝ) (m : ℕ)
    {x : ℝ} (hx : 1 + a * x ≠ 0) :
    iteratedDeriv m (fun y : ℝ ↦ a / (1 + a * y)) x =
      (-1 : ℝ) ^ m * (m.factorial : ℝ) * a ^ (m + 1) /
        (1 + a * x) ^ (m + 1) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      have hne : ∀ᶠ y : ℝ in 𝓝 x, 1 + a * y ≠ 0 :=
        (by fun_prop : ContinuousAt (fun y : ℝ ↦ 1 + a * y) x).eventually_ne hx
      have heq : iteratedDeriv m (fun y : ℝ ↦ a / (1 + a * y)) =ᶠ[𝓝 x]
          (fun y : ℝ ↦ (-1 : ℝ) ^ m * (m.factorial : ℝ) * a ^ (m + 1) /
            (1 + a * y) ^ (m + 1)) := hne.mono fun y hy ↦ ih hy
      rw [iteratedDeriv_succ, heq.deriv_eq,
        (hasDerivAt_const_div_one_add_mul_pow a
          ((-1 : ℝ) ^ m * (m.factorial : ℝ) * a ^ (m + 1)) m hx).deriv]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

end Real
