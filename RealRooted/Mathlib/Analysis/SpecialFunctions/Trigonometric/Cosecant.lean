/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Tactic

/-!
# The differential identity for even cosecant powers

The identity used to induct on the cosecant power in Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2, equation (3.6), follows from a general
second-derivative formula for integer powers of the complex sine.
-/

public section

open Filter Complex
open scoped Topology

namespace Complex

/-- The derivative of an integer power of the sine away from its zeros. -/
theorem hasDerivAt_sin_zpow (m : ℤ) {z : ℂ} (hz : sin z ≠ 0) :
    HasDerivAt (fun w : ℂ => sin w ^ m) ((m : ℂ) * sin z ^ (m - 1) * cos z) z := by
  exact (hasDerivAt_zpow m (sin z) (Or.inl hz)).comp z (hasDerivAt_sin z)

/-- The second derivative of any integer power of the sine away from its zeros. -/
theorem iteratedDeriv_two_sin_zpow (m : ℤ) {z : ℂ} (hz : sin z ≠ 0) :
    iteratedDeriv 2 (fun w : ℂ => sin w ^ m) z =
      (m : ℂ) * (m - 1) * sin z ^ (m - 2) - (m : ℂ) ^ 2 * sin z ^ m := by
  have hevent : deriv (fun w : ℂ => sin w ^ m) =ᶠ[𝓝 z]
      (fun w : ℂ => (m : ℂ) * sin w ^ (m - 1) * cos w) := by
    filter_upwards [continuous_sin.continuousAt.eventually_ne hz] with w hw
    exact (hasDerivAt_sin_zpow m hw).deriv
  have hsecond := (((hasDerivAt_sin_zpow (m - 1) hz).const_mul (m : ℂ)).mul
    (hasDerivAt_cos z)).deriv
  simp only [Pi.mul_def] at hsecond
  have hidx : m - 1 - 1 = m - 2 := by ring
  rw [hidx] at hsecond
  have hpow₁ : sin z ^ (m - 1) * sin z = sin z ^ m := by
    simpa only [zpow_one, sub_add_cancel] using (zpow_add₀ hz (m - 1) 1).symm
  have hpow₂ : sin z ^ (m - 2) * sin z ^ 2 = sin z ^ m := by
    rw [← zpow_natCast, ← zpow_add₀ hz]
    congr 1
    ring
  have hcos : cos z ^ 2 = 1 - sin z ^ 2 := by
    linear_combination sin_sq_add_cos_sq z
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
    hevent.deriv_eq, hsecond]
  push_cast
  calc
    _ = (m : ℂ) * (m - 1) * sin z ^ (m - 2) * cos z ^ 2 -
        m * (sin z ^ (m - 1) * sin z) := by ring
    _ = (m : ℂ) * (m - 1) * sin z ^ (m - 2) * (1 - sin z ^ 2) - m * sin z ^ m := by
      rw [hcos, hpow₁]
    _ = _ := by
      rw [mul_sub, mul_one, mul_assoc ((m : ℂ) * (m - 1)), hpow₂]
      ring

/-- Cao--Fu's differential identity for even powers of the cosecant. -/
theorem iteratedDeriv_two_sin_neg_even_zpow (r : ℕ) {z : ℂ} (hz : sin z ≠ 0) :
    iteratedDeriv 2 (fun w : ℂ => sin w ^ (-(2 * r : ℕ) : ℤ)) z +
        4 * (r : ℂ) ^ 2 * sin z ^ (-(2 * r : ℕ) : ℤ) =
      2 * (r : ℂ) * (2 * r + 1) * sin z ^ (-(2 * (r + 1) : ℕ) : ℤ) := by
  rw [iteratedDeriv_two_sin_zpow _ hz]
  have hidx : (-(2 * r : ℕ) : ℤ) - 2 = -(2 * (r + 1) : ℕ) := by lia
  rw [hidx]
  push_cast
  ring

/-- The even-cosecant differential identity after scaling the argument. -/
theorem iteratedDeriv_two_sin_mul_neg_even_zpow (a : ℂ) (r : ℕ) {z : ℂ}
    (hz : sin (a * z) ≠ 0) :
    iteratedDeriv 2 (fun w : ℂ => sin (a * w) ^ (-(2 * r : ℕ) : ℤ)) z +
        4 * (r : ℂ) ^ 2 * a ^ 2 * sin (a * z) ^ (-(2 * r : ℕ) : ℤ) =
      2 * (r : ℂ) * (2 * r + 1) * a ^ 2 *
        sin (a * z) ^ (-(2 * (r + 1) : ℕ) : ℤ) := by
  have hf : ContDiffAt ℂ 2 (fun w : ℂ => sin w ^ (-(2 * r : ℕ) : ℤ)) (a * z) := by
    simp only [zpow_neg, zpow_natCast]
    exact (Complex.contDiff_sin.contDiffAt.pow (2 * r)).inv (pow_ne_zero _ hz)
  have hlin : iteratedDeriv 2 (fun w : ℂ => a * w) z = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      deriv_const_mul_id']
    simp
  have hcomp := iteratedDeriv_comp_two hf
    (show ContDiffAt ℂ 2 (fun w : ℂ => a * w) z by fun_prop)
  simp only [Function.comp_def, deriv_const_mul_id, hlin, mul_zero, add_zero] at hcomp
  rw [hcomp]
  have h := congrArg (fun v : ℂ => v * a ^ 2) (iteratedDeriv_two_sin_neg_even_zpow r hz)
  linear_combination h

end Complex
