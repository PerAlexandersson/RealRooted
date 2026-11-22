/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic

/-!
# Conjugation and iterated derivatives

Conjugating both the argument and value commutes with every iterated derivative.
In particular, conjugation-invariant functions have real Taylor coefficients at zero.
-/

public section

open scoped ComplexConjugate

/-- Conjugation of the argument and value commutes with every iterated derivative. -/
theorem iteratedDeriv_conj_conj {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [StarRing 𝕜] [NormedStarGroup 𝕜] (f : 𝕜 → 𝕜) (n : ℕ) :
    iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv n f ∘ conj := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, iteratedDeriv_succ]

namespace Complex

/-- Every iterated derivative of a function respecting conjugation respects conjugation. -/
theorem iteratedDeriv_conj {f : ℂ → ℂ} (hf : ∀ z, f (conj z) = conj (f z))
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n f (conj z) = conj (iteratedDeriv n f z) := by
  have hfun : conj ∘ f ∘ conj = f := by
    funext w
    simp [Function.comp_apply, hf]
  have h := congrFun (iteratedDeriv_conj_conj f n) (conj z)
  simpa [hfun, Function.comp_apply] using h

/-- The Taylor data at zero of a conjugation-invariant function are real. -/
theorem ofReal_re_iteratedDeriv_zero {f : ℂ → ℂ}
    (hf : ∀ z, f (conj z) = conj (f z)) (n : ℕ) :
    ((iteratedDeriv n f 0).re : ℂ) = iteratedDeriv n f 0 := by
  apply conj_eq_iff_re.mp
  simpa using (iteratedDeriv_conj hf n 0).symm

end Complex
