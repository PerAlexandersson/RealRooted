/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Conjugation symmetry of the heat operator

A function respecting complex conjugation retains that symmetry after real-time
heat evolution. The simultaneous time/space conjugation formula is valid even
without a convergence hypothesis, since conjugation commutes with total sums.
-/

public section

open scoped ComplexConjugate

namespace Complex

/-- Simultaneous conjugation of time and space commutes with the heat operator
on a function that respects conjugation. -/
theorem heatOperator_conj {f : ℂ → ℂ} (hf : ∀ z, f (conj z) = conj (f z)) (t z : ℂ) :
    heatOperator (conj t) f (conj z) = conj (heatOperator t f z) := by
  unfold heatOperator
  rw [conj_tsum]
  apply tsum_congr
  intro n
  rw [iteratedDeriv_conj hf]
  simp only [map_mul, map_div₀, map_pow, map_neg, map_natCast]

end Complex
