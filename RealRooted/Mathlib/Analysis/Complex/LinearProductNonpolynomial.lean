/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

/-!
# Distinct nonzero slopes force a nonpolynomial linear product
-/

public section

open Polynomial

namespace Complex

/-- Infinitely many distinct nonzero linear factors force the product to
be nonpolynomial. The value at zero excludes the zero polynomial. -/
theorem tprod_one_add_ne_polynomial_of_injective {a : ℕ → ℝ}
    (ha : Function.Injective a) (ha0 : ∀ n, a n ≠ 0) (P : ℂ[X]) :
    (fun z : ℂ ↦ ∏' n, (1 + (a n : ℂ) * z)) ≠ fun z ↦ P.eval z := by
  intro heq
  let r : ℕ → ℂ := fun n ↦ -(a n : ℂ)⁻¹
  have hr : Function.Injective r := by
    intro n m h
    apply ha
    exact Complex.ofReal_injective (inv_injective (neg_injective h))
  have hz (n : ℕ) : P.IsRoot (r n) := by
    change P.eval (r n) = 0
    rw [← congrFun heq (r n)]
    apply tprod_of_exists_eq_zero
    refine ⟨n, ?_⟩
    have hn : (a n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha0 n)
    simp [r, hn]
  have hP : P = 0 := P.eq_zero_of_infinite_isRoot
    ((Set.infinite_range_of_injective hr).mono (by rintro _ ⟨n, rfl⟩; exact hz n))
  have hzero := congrFun heq 0
  simp [hP] at hzero

end Complex
