module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Interval integrals of exponential functions

This file contains a fundamental-theorem-of-calculus identity for exponential
differences.
-/

public section

open scoped Interval

namespace Real

/-- The integral form of the adjacent-difference identity for the exponential kernel. -/
theorem intervalIntegral_mul_exp_mul (a b z : ℝ) :
    (∫ t in a..b, z * exp (t * z)) = exp (b * z) - exp (a * z) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (t * z)).comp t ((hasDerivAt_id t).mul_const z)
  · exact
      (continuous_const.mul
        (Real.continuous_exp.comp (continuous_id.mul continuous_const))).intervalIntegrable _ _

end Real
