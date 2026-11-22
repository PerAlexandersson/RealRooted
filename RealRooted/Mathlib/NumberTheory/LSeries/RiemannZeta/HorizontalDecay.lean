/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.Analysis.MellinInversion.HorizontalDecay
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.GoodHeight
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Choose

/-!
# Vanishing horizontal zeta integrals under RH

A single sequence of symmetric good heights makes both horizontal edges of
the smoothed Perron contour vanish, for every fixed `x ≥ 1`.
-/

public section

open Filter Set MeasureTheory
open scoped Topology Interval

namespace RiemannHypothesis

open Complex

/-- RH supplies symmetric good heights whose horizontal Riesz integrals vanish.

The same sequence works for every fixed `x ≥ 1` and for every choice of the signs
of its heights, so in particular for both horizontal edges of a rectangle. -/
theorem exists_good_height_seq_tendsto_integral_zero (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℕ → ℝ,
      (∀ n : ℕ, t n ∈ Icc ((n : ℝ) + 5) ((n : ℝ) + 5 + 1)) ∧
      Tendsto t atTop atTop ∧
      (∀ n : ℕ, ∀ σ ∈ Icc (9 / 20 : ℝ) 2, ∀ u : ℝ, |u| = t n →
        riemannZeta (σ + I * u) ≠ 0 ∧
          ‖logDeriv riemannZeta (σ + I * u)‖ ≤ C * Real.log ((n : ℝ) + 5) ^ 2) ∧
      ∀ x : ℝ, 1 ≤ x → ∀ u : ℕ → ℝ, (∀ n, |u n| = t n) →
        Tendsto (fun n ↦ ∫ σ in (9 / 20 : ℝ)..2,
          -logDeriv riemannZeta (σ + I * u n) *
            (x : ℂ) ^ ((σ : ℂ) + I * u n + 1) /
              (((σ : ℂ) + I * u n) * ((σ : ℂ) + I * u n + 1))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hg⟩ := hRH.exists_good_height_abs_im
  choose t ht hgood using fun n : ℕ ↦
    hg ((n : ℝ) + 5) (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 5) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine ⟨C, hC, t, ht, tendsto_atTop_mono (fun n ↦ (ht n).1) hnat, hgood, ?_⟩
  intro x hx u hu
  apply Complex.tendsto_horizontal_integral_zero
    (F := fun s ↦ -logDeriv riemannZeta s) (C := C)
    (T := fun n : ℕ ↦ (n : ℝ) + 5) (by norm_num) hx hnat
  · exact Eventually.of_forall fun n ↦ by rw [hu n]; exact (ht n).1
  · exact Eventually.of_forall fun n σ hσ ↦ by
      simpa only [norm_neg] using (hgood n σ hσ (u n) (hu n)).2

end RiemannHypothesis
