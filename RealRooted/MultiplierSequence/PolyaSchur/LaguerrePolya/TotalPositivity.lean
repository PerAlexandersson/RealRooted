module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.PFPolynomial.Closure
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Total positivity of Type-I Laguerre--Pólya Taylor coefficients

The ordinary Taylor coefficients of a Type-I Laguerre--Pólya function form a
Pólya-frequency sequence. The factorial normalization is essential: these are
the coefficients of the ordinary power series, not its exponential Taylor data.
The proof passes every Toeplitz minor to the limit along PF polynomial approximants.
-/

public section

namespace RealRooted

/-- Ordinary Taylor coefficients of a Type-I Laguerre--Pólya function form a
Pólya-frequency sequence, so all their Toeplitz minors are nonnegative. -/
theorem IsLaguerrePolyaTypeI.isPolyaFreqSeq {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) :
    IsPolyaFreqSeq (fun k => (iteratedDeriv k f 0).re / k.factorial) := by
  obtain ⟨p, hp, hlim⟩ := hf
  apply IsPolyaFreqSeq.of_tendsto (fun n => (hp n).to_sequence)
  intro k
  simpa only [Complex.div_natCast_re] using
    Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim k

end RealRooted
