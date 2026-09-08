module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

public section

open Filter Topology

namespace Matrix

variable {ι : Type*} [PartialOrder ι]

/-- A continuous curve of totally nonnegative real matrices for positive
parameters has a totally nonnegative value at zero. -/
theorem IsTotallyNonneg.of_continuous_curve
    {A : ℝ → Matrix ι ι ℝ} (hA : Continuous A)
    (hpos : ∀ {r : ℝ}, 0 < r → (A r).IsTotallyNonneg) :
    (A 0).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  let D : ℝ → ℝ := fun r ↦ ((A r).submatrix rows cols).det
  have hD_cont : Continuous D :=
    (hA.matrix_submatrix rows cols).matrix_det
  have hD_lim :
      Tendsto D (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (D 0)) :=
    hD_cont.continuousAt.continuousWithinAt
  have hzero_lim : Tendsto (fun _ : ℝ ↦ (0 : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_const_nhds
  exact le_of_tendsto_of_tendsto hzero_lim hD_lim (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hpos hr hrows hcols)

end Matrix
