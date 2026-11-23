/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Uniform finite nonvanishing jets of entire functions

A nonzero entire function has a nonvanishing derivative at every point.
Compactness gives one finite jet length that works throughout a compact set.
-/

public section

namespace Complex

/-- A nonzero entire function has a finite nonvanishing Taylor jet at every point. -/
theorem exists_iteratedDeriv_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f ≠ 0) (z : ℂ) : ∃ k : ℕ, iteratedDeriv k f z ≠ 0 := by
  have hfinite : analyticOrderAt f z ≠ ⊤ := by
    exact (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => hf.analyticAt w)).not.mpr hf0
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfinite
  exact ⟨k, ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (hf.analyticAt z)).mp hk.symm).2⟩

/-- A compact set admits a uniform bound on the index of a nonvanishing
Taylor derivative of a nonzero entire function. The compact set may be empty. -/
theorem exists_uniform_iteratedDeriv_ne_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ z ∈ K, ∃ k < N, iteratedDeriv k f z ≠ 0 := by
  have hopen (k : ℕ) : IsOpen {z | iteratedDeriv k f z ≠ 0} :=
    isOpen_ne_fun (((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k
      (WithTop.coe_lt_top _)).continuous) continuous_const
  have hcover : K ⊆ ⋃ k : ℕ, {z | iteratedDeriv k f z ≠ 0} := by
    intro z _
    obtain ⟨k, hk⟩ := exists_iteratedDeriv_ne_zero hf hf0 z
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun k : ℕ => {z | iteratedDeriv k f z ≠ 0}) hopen hcover
  refine ⟨s.sup id + 1, ?_⟩
  intro z hz
  obtain ⟨k, hk, hne⟩ : ∃ k, k ∈ s ∧ iteratedDeriv k f z ≠ 0 := by
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hs hz
  exact ⟨k, Nat.lt_succ_of_le (Finset.le_sup (f := id) hk), hne⟩

end Complex
