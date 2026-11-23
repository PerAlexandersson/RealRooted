module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Hermite.FormalDifferential.Structure

/-!
# Exact degree of exponential-stride differential images
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- An expanded formal exponential sends a monomial to a monic polynomial
of the same degree, for every real parameter and positive stride. -/
theorem isMonicOfDegree_formal_exp_stride (β : ℝ) {p : ℕ} (hp : 0 < p) (d : ℕ) :
    IsMonicOfDegree (formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ d)) d := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.expand p hp.ne'
      (PowerSeries.rescale β (PowerSeries.exp ℝ))) = 1 := by
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  refine ⟨?_, formalDifferentialOperator_monic h0 (monic_X.pow d)⟩
  rw [natDegree_formalDifferentialOperator (by rw [h0]; exact one_ne_zero)
    (pow_ne_zero d X_ne_zero), natDegree_X_pow]

end RealRooted.HermitePoulain
