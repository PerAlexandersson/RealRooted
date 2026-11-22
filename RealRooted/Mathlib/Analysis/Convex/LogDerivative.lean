/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic concavity from a differential inequality

The inequality `f'² - f f'' ≥ 0` implies concavity of `log |f|` on every
zero-free interval. Real logarithms already satisfy `log f = log |f|`, so
negative functions require no separate sign assumption.
-/

public section

/-- The differential inequality `f'² - f f'' ≥ 0` implies logarithmic
concavity on a convex zero-free set. -/
theorem concaveOn_log_of_deriv_sq_sub_nonneg {f f' f'' : ℝ → ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (hf : ∀ x ∈ S, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ S, HasDerivAt f' (f'' x) x)
    (hne : ∀ x ∈ S, f x ≠ 0)
    (hL : ∀ x ∈ S, 0 ≤ f' x ^ 2 - f x * f'' x) :
    ConcaveOn ℝ S (fun x => Real.log (f x)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hS
    (f' := fun x => f' x / f x)
    (f'' := fun x => (f'' x * f x - f' x * f' x) / f x ^ 2)
  · intro x hx
    exact ((hf x hx).log (hne x hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact ((hf x (interior_subset hx)).log (hne x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact ((hf' x (interior_subset hx)).div (hf x (interior_subset hx))
      (hne x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    nlinarith [hL x (interior_subset hx)]
