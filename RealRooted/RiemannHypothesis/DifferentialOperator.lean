module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.RiemannHypothesis
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorCriterion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

/-!
# Xi differential operators and the Riemann hypothesis

Under RH, every derivative of the square-variable xi function defines a
constant-coefficient differential operator preserving real-rootedness.
The unshifted operator's preservation property already characterizes RH.
On polynomials, each operator is a finite sum, so no convergence assumption
on infinite differential series is needed.

This specializes the operator argument in Section 3.1 of O'Sullivan,
*Zeros of Jensen polynomials and asymptotics for the Riemann xi function*,
https://arxiv.org/abs/2007.13582.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Under RH, the Taylor differential operator of every derivative of xi's
square-variable function preserves real-rootedness. -/
theorem taylorDifferentialOperator_riemannXiTheta_splits (hRH : RiemannHypothesis)
    (n : ℕ) {p : ℝ[X]} (hp : p.Splits) :
    (taylorDifferentialOperator (iteratedDeriv n riemannXiTheta) p).Splits :=
  IsLaguerrePolya.taylorDifferentialOperator_splits
    ((riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n) hp

/-- RH is equivalent to the unshifted xi Taylor differential operator
preserving real-rootedness. -/
theorem riemannHypothesis_iff_taylorDifferentialOperator_splits :
    RiemannHypothesis ↔ ∀ p : ℝ[X], p.Splits →
      (taylorDifferentialOperator riemannXiTheta p).Splits := by
  rw [riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta]
  exact isLaguerrePolya_iff_taylorDifferentialOperator_splits
    differentiable_riemannXiTheta riemannXiTheta_conj

end RealRooted
