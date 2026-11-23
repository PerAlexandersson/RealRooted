/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.Ring

/-!
# Partial-fraction bounds away from the support

A finite sum of simple-pole terms with nonnegative integer multiplicities is bounded by
the total multiplicity divided by the distance from its support. This applies to polynomial
logarithmic derivatives and local divisor sums of analytic functions.
-/

public section

namespace Complex

/-- A separated finite partial-fraction sum is bounded by total multiplicity over separation. -/
theorem norm_finsum_intCast_div_sub_le {D : ℂ → ℤ} (hfin : Function.HasFiniteSupport D)
    (hnonneg : ∀ ρ, 0 ≤ D ρ) {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ ρ ∈ Function.support D, δ ≤ ‖s - ρ‖) :
    ‖∑ᶠ ρ, (D ρ : ℂ) / (s - ρ)‖ ≤ δ⁻¹ * ((∑ᶠ ρ, D ρ : ℤ) : ℝ) := by
  classical
  have hsub : Function.support (fun ρ ↦ (D ρ : ℂ) / (s - ρ)) ⊆ hfin.toFinset := by
    intro ρ hρ
    exact hfin.mem_toFinset.mpr fun h ↦ hρ (by simp [h])
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum D hfin,
    Int.cast_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
  have hDρ : 0 ≤ (D ρ : ℝ) := Int.cast_nonneg (hnonneg ρ)
  rw [norm_div, Complex.norm_intCast, abs_of_nonneg hDρ]
  calc
    (D ρ : ℝ) / ‖s - ρ‖ ≤ (D ρ : ℝ) / δ :=
      div_le_div_of_nonneg_left hDρ hδ (hsep ρ (hfin.mem_toFinset.mp hρ))
    _ = δ⁻¹ * (D ρ : ℝ) := by ring

end Complex
