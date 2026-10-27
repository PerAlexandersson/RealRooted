/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Splitting of derivatives of real polynomials

This file provides the `Splits` consequences of Rolle's theorem needed by
the real-rooted polynomial development.
-/

public section

open Polynomial

namespace Polynomial

/-- The derivative of a real polynomial that splits also splits. -/
theorem Splits.derivative {p : ℝ[X]} (hp : p.Splits) : p.derivative.Splits := by
  rw [splits_iff_card_roots]
  have hupper : p.derivative.roots.card ≤ p.natDegree - 1 := by
    simpa only [natDegree_derivative] using card_roots' p.derivative
  have hlower : p.natDegree ≤ p.derivative.roots.card + 1 := by
    simpa only [hp.natDegree_eq_card_roots] using card_roots_le_derivative p
  simpa only [natDegree_derivative] using Nat.le_antisymm hupper (by lia)

/-- Every iterate of the derivative of a splitting real polynomial splits. -/
theorem Splits.iterate_derivative {p : ℝ[X]} (hp : p.Splits) (k : ℕ) :
    (Polynomial.derivative^[k] p).Splits := by
  induction k with
  | zero => simpa
  | succ k ih => simpa [Function.iterate_succ_apply'] using ih.derivative

end Polynomial
