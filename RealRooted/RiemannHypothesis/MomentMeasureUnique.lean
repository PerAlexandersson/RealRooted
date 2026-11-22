module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasureUnique
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# Unique logarithmic-derivative moment measures under RH

Under Mathlib's RH, each derivative of the normalized square-variable xi
function has a unique positive measure representing its signed logarithmic-
derivative Taylor coefficients. Competitors are arbitrary measures on the real
line with integrable power moments.
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- RH gives a unique genuine moment measure for the signed logarithmic
coefficients of every derivative of the normalized square-variable xi function. -/
theorem existsUnique_logDeriv_riemannXiTheta_moment_measure
    (hRH : RiemannHypothesis) (s : ℕ) :
    ∃! mu : Measure ℝ, ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
      (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv (iteratedDeriv s riemannXiTheta)) 0 /
        k.factorial = ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).existsUnique_logDeriv_moment_measure
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)

end RealRooted
