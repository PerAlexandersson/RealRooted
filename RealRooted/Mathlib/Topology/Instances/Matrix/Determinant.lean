import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Determinants of convergent finite matrices

This file exposes the entrywise-continuity interface for finite determinants.
-/

open Filter Topology

namespace Matrix

/-- The determinant is continuous along entrywise-converging sequences. -/
theorem tendsto_det {R n : Type*} [TopologicalSpace R] [CommRing R]
    [IsTopologicalRing R] [Fintype n] [DecidableEq n]
    {M : ℕ → Matrix n n R} {M₀ : Matrix n n R}
    (h : ∀ i j, Tendsto (fun k => M k i j) atTop (𝓝 (M₀ i j))) :
    Tendsto (fun k => (M k).det) atTop (𝓝 M₀.det) := by
  simp only [Matrix.det_apply]
  refine tendsto_finsetSum _ fun σ _ => ?_
  exact Tendsto.const_smul (tendsto_finsetProd _ fun i _ => h (σ i) i) _

/-- Nonnegative determinants remain nonnegative under entrywise limits of
finite real matrices. -/
theorem det_nonneg_of_tendsto {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℕ → Matrix n n ℝ} {M₀ : Matrix n n ℝ}
    (hM : ∀ᶠ k in atTop, 0 ≤ (M k).det)
    (h : ∀ i j, Tendsto (fun k => M k i j) atTop (𝓝 (M₀ i j))) :
    0 ≤ M₀.det := by
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_det h)
    hM

end Matrix
