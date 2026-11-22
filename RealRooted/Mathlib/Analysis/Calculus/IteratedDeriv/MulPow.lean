/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Taylor data after multiplication by a monomial
-/

public section

/-- Multiplication by a monomial shifts Taylor coefficients at zero. -/
theorem iteratedDeriv_pow_mul_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} {n : ℕ} (hf : ContDiffAt 𝕜 n f 0) (m : ℕ) :
    iteratedDeriv n (fun z => z ^ m * f z) 0 =
      (n.choose m : 𝕜) * m.factorial * iteratedDeriv (n - m) f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf]
  simp only [iteratedDeriv_fun_pow_zero]
  by_cases hm : m ≤ n
  · simp [Finset.sum_ite_eq', hm]
  · simp [Finset.sum_ite_eq', hm, Nat.choose_eq_zero_of_lt (lt_of_not_ge hm)]
