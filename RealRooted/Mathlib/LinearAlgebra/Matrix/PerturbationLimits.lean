/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform inverse bounds near a nonsingular real matrix

Convergence to a nonsingular finite real matrix gives eventual nonsingularity
and one positive bound for every entry of the inverses.
-/

public section

open Filter Topology

namespace Matrix

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {l : Filter ι} {A : ι → Matrix κ κ ℝ} {A₀ : Matrix κ κ ℝ}

/-- The total matrix inverse converges at a nonsingular real matrix. -/
theorem tendsto_nonsing_inv_of_isUnit_det
    (hA : Tendsto A l (𝓝 A₀)) (hdet : IsUnit A₀.det) :
    Tendsto (fun t ↦ (A t)⁻¹) l (𝓝 A₀⁻¹) := by
  have hi : ContinuousAt (Ring.inverse : ℝ → ℝ) A₀.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp hdet)
  exact (continuousAt_matrix_inv A₀ hi).tendsto.comp hA

/-- Near a nonsingular real matrix, inverses exist and their entries admit
one uniform positive bound. -/
theorem eventually_isUnit_det_and_inv_bound
    (hA : Tendsto A l (𝓝 A₀)) (hdet : IsUnit A₀.det) :
    ∃ M > 0, ∀ᶠ t in l, IsUnit (A t).det ∧ ∀ i j, |(A t)⁻¹ i j| ≤ M := by
  let M : ℝ := 1 + ∑ i : κ, ∑ j : κ, |A₀⁻¹ i j|
  have hM : 0 < M := by dsimp [M]; positivity
  have hentry (i j : κ) : |A₀⁻¹ i j| < M := by
    have hj : |A₀⁻¹ i j| ≤ ∑ k : κ, |A₀⁻¹ i k| :=
      Finset.single_le_sum (fun k _ ↦ abs_nonneg (A₀⁻¹ i k)) (Finset.mem_univ j)
    have hi : (∑ k : κ, |A₀⁻¹ i k|) ≤ ∑ r : κ, ∑ k : κ, |A₀⁻¹ r k| :=
      Finset.single_le_sum (f := fun r : κ ↦ ∑ k : κ, |A₀⁻¹ r k|)
        (fun r _ ↦ Finset.sum_nonneg (fun k _ ↦ abs_nonneg (A₀⁻¹ r k)))
        (Finset.mem_univ i)
    dsimp only [M]
    linarith
  have hdetc : Continuous (fun B : Matrix κ κ ℝ ↦ B.det) :=
    continuous_id.matrix_det
  have hdetlim := (hdetc.tendsto A₀).comp hA
  have hunit : ∀ᶠ t in l, IsUnit (A t).det := by
    filter_upwards [hdetlim.eventually_ne (isUnit_iff_ne_zero.mp hdet)] with t ht
    exact isUnit_iff_ne_zero.mpr ht
  have hinv := tendsto_nonsing_inv_of_isUnit_det hA hdet
  have hbound : ∀ᶠ t in l, ∀ i j : κ, |(A t)⁻¹ i j| ≤ M := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hij := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i) j
    exact (hij.abs.eventually_lt tendsto_const_nhds (hentry i j)).mono fun _ h ↦ h.le
  exact ⟨M, hM, hunit.and hbound⟩

end Matrix
