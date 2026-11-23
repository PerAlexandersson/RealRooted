/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Complex.Basic

/-!
# Repeating summable nonnegative terms with finite multiplicities

A nonnegative weighted sum is summable exactly when the family obtained by
repeating every term its natural multiplicity is summable. Grouping convergent
complex resolvent sums over these finite fibers is equally explicit.
-/

public section

/-- Summability with natural multiplicities gives summability of the repeated
nonnegative family, without choosing an enumeration. -/
theorem summable_sigma_fin_of_nonneg {ι : Type*} {a : ι → ℝ} (m : ι → ℕ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable (fun i ↦ (m i : ℝ) * a i)) :
    Summable (fun j : Σ i, Fin (m i) ↦ a j.1) := by
  apply (summable_sigma_of_nonneg (fun j ↦ ha j.1)).mpr
  refine ⟨fun _ ↦ Summable.of_finite, ?_⟩
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] using hs

/-- Grouping a convergent resolvent sum over its finite multiplicity fibers. -/
theorem HasSum.sigma_fin_const_div {ι : Type*} {a : ι → ℝ} {m : ι → ℕ}
    {z s : ℂ}
    (h : HasSum (fun j : Σ i, Fin (m i) ↦ (a j.1 : ℂ) / (1 + (a j.1 : ℂ) * z)) s) :
    HasSum (fun i ↦ (m i : ℂ) * (a i : ℂ) / (1 + (a i : ℂ) * z)) s := by
  apply h.sigma
  intro i
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_assoc] using
    hasSum_fintype (fun _ : Fin (m i) ↦ (a i : ℂ) / (1 + (a i : ℂ) * z))

end
