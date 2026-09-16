module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

public section

open Filter Topology

namespace Matrix

variable {ι : Type*} [PartialOrder ι]

/-- Entrywise sequential limits of totally nonnegative real matrices are
totally nonnegative. -/
theorem IsTotallyNonneg.of_tendsto
    {A : ℕ → Matrix ι ι ℝ} {A₀ : Matrix ι ι ℝ}
    (hA : ∀ k, (A k).IsTotallyNonneg)
    (hlim : ∀ i j, Tendsto (fun k => A k i j) atTop (𝓝 (A₀ i j))) :
    A₀.IsTotallyNonneg := by
  intro n rows cols hrows hcols
  have hmatrix : Tendsto
      (fun k => (A k).submatrix rows cols) atTop
      (𝓝 (A₀.submatrix rows cols)) := by
    exact tendsto_pi_nhds.mpr fun i =>
      tendsto_pi_nhds.mpr fun j => hlim (rows i) (cols j)
  have hdet : Tendsto
      (fun k => ((A k).submatrix rows cols).det) atTop
      (𝓝 ((A₀.submatrix rows cols).det)) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  exact ge_of_tendsto hdet <| Eventually.of_forall fun k => hA k hrows hcols

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
