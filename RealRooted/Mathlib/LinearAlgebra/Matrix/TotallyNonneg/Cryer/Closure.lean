import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer.Strict
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularStrictification
import RealRooted.Mathlib.Topology.Instances.Matrix.Determinant

/-!
# The nonsingular finite Cryer closure

This leaf turns nonnegative initial-column minors of a nonsingular
upper-triangular matrix into total nonnegativity.  The proof strictifies the
consecutive minors by Gaussian multiplication, applies the strict
consecutive-column criterion, and passes to the Gaussian limit.
-/

open Filter Topology

namespace Matrix

/-- A nonsingular upper-triangular real matrix with nonnegative initial-column
minors is totally nonnegative. -/
theorem HasNonnegInitialColumnMinors.isTotallyNonneg_of_upper_zero_of_det_ne_zero
    {N : Nat} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.HasNonnegInitialColumnMinors)
    (hupper : ∀ i j, i < j → A i j = 0) (hdet : A.det ≠ 0) :
    A.IsTotallyNonneg := by
  have hAinj : Function.Injective A.mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply A.isUnit_iff_isUnit_det.mpr
    exact isUnit_iff_ne_zero.mpr hdet
  intro k rows cols hrows hcols
  let D : ℝ → ℝ := fun a =>
    ((gaussianMatrix N a * A).submatrix rows cols).det
  have hDlim : Tendsto D atTop (𝓝 ((A.submatrix rows cols).det)) := by
    exact ((continuous_id.matrix_submatrix rows cols).matrix_det.continuousAt.tendsto).comp
      (tendsto_gaussianMatrix_mul_atTop A)
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hDlim ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hBconsecutive : ∀ {m c : Nat} (hmc : c + m ≤ N)
      (sourceRows : Fin m → Fin N), StrictMono sourceRows →
      0 < ((gaussianMatrix N a * A).submatrix sourceRows
        (fun j => Fin.castLE hmc (Fin.natAdd c j))).det := by
    intro m c hmc sourceRows hsourceRows
    have hsourceCols : StrictMono (fun j : Fin m => Fin.castLE hmc (Fin.natAdd c j)) :=
      (Fin.strictMono_castLE hmc).comp (Fin.strictMono_natAdd c)
    apply det_gaussianMatrix_mul_pos_of_fixed_column_minors hAinj ha hsourceRows hsourceCols
    intro sourceRows' hsourceRows'
    exact hA.consecutiveColumnMinor_nonneg A hupper hdet hmc sourceRows' hsourceRows'
  exact (pos_minor_of_pos_consecutive_column_minors (gaussianMatrix N a * A)
    hBconsecutive rows cols hrows hcols).le

end Matrix
