import Mathlib.Topology.Instances.Matrix

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

end Matrix
