module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import Mathlib.Algebra.Group.ForwardDiff
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.RiemannHypothesis.JensenSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.ForwardDifference
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity

/-!
# Negative signed forward differences of xi coefficients under RH

For every fixed derivative shift, RH forces a negative signed forward difference
of some positive order. The proof uses the negative real zeros of that xi
derivative and the Taylor series after multiplication by `exp(-z)`.

This is a derived consequence. Its quantifiers differ from eventual positivity
in the shift for each fixed difference order.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, at every coefficient shift some positive-order signed forward
difference of the normalized xi coefficients is strictly negative. -/
theorem exists_signed_fwdDiff_iter_riemannXiCoeff_neg
    (hRH : RiemannHypothesis) (s : ℕ) :
    ∃ r : ℕ, r ≠ 0 ∧ (-1 : ℝ) ^ r * ((fwdDiff 1)^[r] riemannXiCoeff) s < 0 := by
  have hf := isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s
  obtain ⟨r, hr, hneg⟩ := hf.exists_signed_fwdDiff_iter_neg
    (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta s)
    (by norm_num) (riemannXiCoeff_pos s) (iteratedDeriv_riemannXiTheta_ne_polynomial s)
  refine ⟨r, hr, ?_⟩
  have heq : (fun k => (iteratedDeriv k (iteratedDeriv s riemannXiTheta) 0).re) =
      fun k => riemannXiCoeff (k + s) := by
    funext k
    simp only [riemannXiCoeff, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]
  rw [heq, fwdDiff_iter_comp_add, zero_add] at hneg
  exact hneg

end RealRooted
