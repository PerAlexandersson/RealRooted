module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.RiemannHypothesis.MultiplierSequence
import RealRooted.MultiplierSequence.Arithmetic

/-!
# Arithmetic xi multiplier sequences under RH

Pólya's arithmetic-section theorem applied to the normalized xi coefficients
under RH gives new Type-I entire functions, multiplier sequences and totally
nonnegative Toeplitz matrices at every stride and starting index.
-/

public section

namespace RealRooted

/-- Under RH, every arithmetic subsequence of normalized xi coefficients is
a PF multiplier sequence. -/
theorem isPFMultiplierSequence_riemannXiCoeff_arithmetic
    (hRH : RiemannHypothesis) (r s : ℕ) :
    IsPFMultiplierSequence (fun k => riemannXiCoeff (s + r * k)) :=
  (isPFMultiplierSequence_riemannXiCoeff hRH).arithmetic r s

/-- Under RH, every arithmetic exponential section of the xi coefficients
is an entire positive Type-I Laguerre--Pólya function. -/
theorem isLaguerrePolyaTypeI_riemannXiCoeff_arithmetic
    (hRH : RiemannHypothesis) (r s : ℕ) :
    IsLaguerrePolyaTypeI
      (complexExpGeneratingFunction (fun k => riemannXiCoeff (s + r * k))) :=
  (isPFMultiplierSequence_riemannXiCoeff hRH).isLaguerrePolyaTypeI_arithmetic r s

/-- Under RH, every factorial-normalized arithmetic xi sequence has all
Toeplitz minors nonnegative. -/
theorem isPolyaFreqSeq_riemannXiCoeff_arithmetic_div_factorial
    (hRH : RiemannHypothesis) (r s : ℕ) :
    IsPolyaFreqSeq (fun k => riemannXiCoeff (s + r * k) / k.factorial) :=
  (isPFMultiplierSequence_riemannXiCoeff_arithmetic hRH r s).isPolyaFreqSeq_div_factorial

end RealRooted
