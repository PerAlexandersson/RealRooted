/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Conjugation symmetry of infinite differential sums

Real entire symbols act on real entire targets by real entire differential
sums whenever those sums converge. The conjugation identity itself also
holds for the total sum without a convergence assumption.
-/

public section

open scoped ComplexConjugate

namespace Complex

/-- Infinite differential sums respect conjugation when both inputs do. -/
theorem infiniteDifferentialApply_conj {φ f : ℂ → ℂ}
    (hφ : ∀ z, φ (conj z) = conj (φ z)) (hf : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    infiniteDifferentialApply φ f (conj z) = conj (infiniteDifferentialApply φ f z) := by
  unfold infiniteDifferentialApply
  rw [conj_tsum]
  apply tsum_congr
  intro n
  rw [iteratedDeriv_conj hf]
  have hφn : conj (iteratedDeriv n φ 0) = iteratedDeriv n φ 0 := by
    simpa only [map_zero] using (iteratedDeriv_conj hφ n 0).symm
  simp only [map_div₀, map_mul, map_natCast, hφn]

end Complex
