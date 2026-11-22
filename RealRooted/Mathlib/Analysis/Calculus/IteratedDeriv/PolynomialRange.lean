/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Padding finite differential operators to a larger degree
-/

public section

namespace Polynomial

/-- A polynomial differential operator may be summed up to any degree bound
for its symbol. No differentiability hypothesis on the input is needed. -/
theorem differentialApply_eq_sum_range {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (p : 𝕜[X]) (f : 𝕜 → E) {N : ℕ}
    (hN : p.natDegree ≤ N) (z : 𝕜) :
    p.differentialApply f z =
      ∑ k ∈ Finset.range (N + 1), p.coeff k • iteratedDeriv k f z := by
  unfold differentialApply
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [coeff_eq_zero_of_natDegree_lt (by lia), zero_smul]

end Polynomial
