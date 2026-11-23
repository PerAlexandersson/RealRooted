module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

public import RealRooted.Hermite.Generalized.Basic
public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
import RealRooted.Hermite.FormalDifferential.ExpandOperator
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient

/-!
# Generalized Hermite polynomials as actual formal differential images
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- Expanded formal exponentials act by the finite exponential derivative sum. -/
theorem formalDifferentialOperator_exp_stride_eq_sum
    (β : ℝ) {p : ℕ} (hp : 0 < p) (P : ℝ[X]) :
    formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ))) P =
      ∑ k ∈ Finset.range (P.natDegree / p + 1),
        C (β ^ k / (k.factorial : ℝ)) * (derivative^[p * k]) P := by
  rw [formalDifferentialOperator_expand_eq_sum _ hp]
  simp only [PowerSeries.coeff_rescale_exp]

/-- The normalized negative exponential limit is exactly the generalized Hermite family. -/
theorem formalDifferentialOperator_exp_neg_stride_X_pow
    {p : ℕ} (hp : 0 < p) (d : ℕ) :
    formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale (-1) (PowerSeries.exp ℝ))) (X ^ d) =
      generalizedHermite p d := by
  rw [formalDifferentialOperator_exp_stride_eq_sum _ hp, natDegree_X_pow]
  rfl

end RealRooted.HermitePoulain
