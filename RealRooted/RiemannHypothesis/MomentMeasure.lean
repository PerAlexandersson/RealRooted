module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta

import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasure
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative

/-!
# Positive moment measures for xi logarithmic derivatives under RH

Under RH, the signed logarithmic-derivative coefficients of every derivative
of the square-variable xi function have an explicit finite positive measure
with compact nonnegative support.
-/

public section

open Complex MeasureTheory

namespace RealRooted

/-- Under RH, every xi derivative has a positive compactly supported moment
measure for the actual signed complex coefficients of its logarithmic derivative. -/
theorem exists_logDeriv_riemannXiTheta_moment_measure
    (hRH : RiemannHypothesis) (s : ℕ) :
    ∃ (gamma : ℝ) (a : ℕ → ℝ) (mu : Measure ℝ),
      0 ≤ gamma ∧ (∀ i, 0 ≤ a i) ∧ Summable a ∧
      mu = ENNReal.ofReal gamma • Measure.dirac 0 +
        Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)) ∧
      IsFiniteMeasure mu ∧ mu (Set.Icc 0 (∑' i, a i))ᶜ = 0 ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
        (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv (iteratedDeriv s riemannXiTheta)) 0 /
          k.factorial = ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).exists_logDeriv_moment_measure
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)

end RealRooted
