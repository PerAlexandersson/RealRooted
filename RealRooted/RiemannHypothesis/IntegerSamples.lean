module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.MultiplierSequence.Infinite
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.MultiplierSequence.Laguerre

/-!
# Integer sample values of xi derivatives as multiplier sequences

Laguerre's sample-value theorem applies to every Type-I xi derivative under RH.
The sequence consists of values at nonnegative integers, rather than Taylor
coefficients at the origin.
-/

public section

open Complex

namespace RealRooted

/-- Under RH the values of each xi derivative at nonnegative integers form
a PF multiplier sequence. -/
theorem isPFMultiplierSequence_iteratedDeriv_riemannXiTheta_natCast
    (hRH : RiemannHypothesis) (n : ℕ) :
    IsPFMultiplierSequence (fun k => (iteratedDeriv n riemannXiTheta k).re) :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n).isPFMultiplierSequence_eval_natCast

end RealRooted
