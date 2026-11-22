module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIInfiniteDifferential

/-!
# Positive Type-I xi differential images under RH

Under Mathlib's Riemann hypothesis every derivative of the square-variable xi
function is positive Type-I. Pólya's positive Type-I infinite differential
theorem therefore applies with xi as symbol or target. The actual series
converges everywhere and no convergence or growth premise is needed.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, every differentiated xi symbol maps positive Type-I entire
targets to positive Type-I entire functions by the actual differential series. -/
theorem isLaguerrePolyaTypeI_riemannXi_infiniteDifferentialApply
    (hRH : RiemannHypothesis) (n : ℕ) {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) :
    IsLaguerrePolyaTypeI (Complex.infiniteDifferentialApply (iteratedDeriv n riemannXiTheta) f) :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n).infiniteDifferentialApply hf

/-- Under RH, every positive Type-I differential symbol maps each derivative
of xi to a positive Type-I entire function, with convergence automatic. -/
theorem isLaguerrePolyaTypeI_infiniteDifferentialApply_riemannXi
    (hRH : RiemannHypothesis) (n : ℕ) {φ : ℂ → ℂ} (hφ : IsLaguerrePolyaTypeI φ) :
    IsLaguerrePolyaTypeI (Complex.infiniteDifferentialApply φ (iteratedDeriv n riemannXiTheta)) :=
  hφ.infiniteDifferentialApply (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n)

end RealRooted
