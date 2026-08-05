import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularStrictification
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariationTopology
import RealRooted.Mathlib.LinearAlgebra.Matrix.VariationDiminishing

/-!
# Variation bounds for sign-consistent matrices

This file proves the full-column-rank case of the variation bound in Karlin,
*Total Positivity*, Volume I, Chapter V, Section 1, Theorem 1.3. Gaussian
strictification reduces the result to the strict maximal-minor theorem, and
lower semicontinuity of sign variations passes the bound to the limit.
-/

open Filter

/-- A full-column-rank sign-consistent matrix has at most `q - 1` sign
variations in every vector in its range. -/
theorem Matrix.IsSignConsistentOrder.signVariations_mulVec_le_card_sub_one
    {m q : ℕ} {A : Matrix (Fin m) (Fin q) ℝ}
    (hA : A.IsSignConsistentOrder q)
    (hqm : q ≤ m)
    (hAinj : Function.Injective A.mulVec)
    (x : Fin q → ℝ) :
    Fin.signVariations (A.mulVec x) ≤ q - 1 := by
  refine Fin.signVariations_le_of_tendsto
    (l := (atTop : Filter ℝ))
    (f := fun a => (Matrix.gaussianMatrix m a * A).mulVec x) ?_ ?_
  · have hcont : Continuous
        (fun M : Matrix (Fin m) (Fin q) ℝ => M.mulVec x) :=
      continuous_id.matrix_mulVec continuous_const
    exact hcont.continuousAt.tendsto.comp
      (Matrix.tendsto_gaussianMatrix_mul_atTop A)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with a ha
    have hstrict :
        (Matrix.gaussianMatrix m a * A).IsStrictlySignConsistentOrder q :=
      hA.isStrictlySignConsistentOrder_gaussianMatrix_mul hAinj ha
    exact Matrix.signVariations_mulVec_le_card_sub_one_of_strictMaximalMinors
      hqm (fun ⦃rows rows'⦄ hrows hrows' =>
        hstrict hrows hrows' strictMono_id strictMono_id) x
