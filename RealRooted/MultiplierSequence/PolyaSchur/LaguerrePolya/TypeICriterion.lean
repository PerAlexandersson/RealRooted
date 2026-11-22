module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivity
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# The positive Laguerre--Pólya subclass

The PF polynomial approximation definition of positive Type-I functions is
equivalent to membership in the Laguerre--Pólya class with nonnegative Taylor
data. This is the class denoted LP+ by Craven and Csordas. Zero is included.
-/

public section

namespace RealRooted

/-- An LP function with nonnegative Taylor data has PF polynomial approximants. -/
theorem IsLaguerrePolya.isLaguerrePolyaTypeI_of_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hpos : ∀ k, 0 ≤ (iteratedDeriv k f 0).re) :
    IsLaguerrePolyaTypeI f := by
  have hpf : IsPFMultiplierSequence (fun k => (iteratedDeriv k f 0).re) := by
    apply isPFMultiplierSequence_iff_jensenPolynomial_isPF.mpr
    intro d
    exact IsPFPolynomial.of_realRooted_nonneg (hasNonnegCoeffs_jensenPolynomial hpos)
      (hf.jensenPolynomial_splits d)
  have hreal (k : ℕ) : iteratedDeriv k f 0 = ((iteratedDeriv k f 0).re : ℂ) :=
    (Complex.ofReal_re_iteratedDeriv_zero hf.conj k).symm
  rw [eq_complexExpGeneratingFunction_of_iteratedDeriv hf.differentiable hreal]
  exact hpf.isLaguerrePolyaTypeI_complexExpGeneratingFunction

/-- Positive Type-I means LP membership together with nonnegative Taylor data. -/
theorem isLaguerrePolyaTypeI_iff_isLaguerrePolya_nonneg {f : ℂ → ℂ} :
    IsLaguerrePolyaTypeI f ↔
      IsLaguerrePolya f ∧ ∀ k, 0 ≤ (iteratedDeriv k f 0).re := by
  constructor
  · intro hf
    refine ⟨hf.toLaguerrePolya, fun k => ?_⟩
    have h := hf.isPolyaFreqSeq.nonneg k
    simpa only [zero_mul] using (le_div_iff₀ (by positivity)).mp h
  · rintro ⟨hf, hp⟩
    exact hf.isLaguerrePolyaTypeI_of_nonneg hp

end RealRooted
