module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import RealRooted.LaguerreInequalities.Analytic
public import RealRooted.BrandenLC.Sequence
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Iterated log-concavity of Laguerre--Pólya coefficients

All iterated log-concavity transforms of the ordinary Taylor coefficients of a
positive Type-I function are PF sequences. The same holds for the generalized
Laguerre coefficients at each real point of any Laguerre--Pólya function.
These statements use PF polynomial approximation and Brändén's finite theorem.
-/

public section

namespace RealRooted

/-- Every log-concavity iterate of a positive Type-I function's ordinary
Taylor coefficients is a Pólya-frequency sequence. -/
theorem IsLaguerrePolyaTypeI.isPolyaFreqSeq_iterate_logConcavity {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) (m : ℕ) :
    IsPolyaFreqSeq ((logConcavitySequence^[m])
      (fun k => (iteratedDeriv k f 0).re / k.factorial)) := by
  obtain ⟨p, hp, hlim⟩ := hf
  apply isPolyaFreqSeq_iterate_logConcavitySequence_of_limit hp ?_ m
  intro k
  simpa only [Complex.div_natCast_re] using
    Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim k

/-- A positive ordinary Taylor coefficient of a Type-I function remains
positive under every log-concavity iterate. -/
theorem IsLaguerrePolyaTypeI.iterate_logConcavity_pos {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) (m k : ℕ) (hk : 0 < (iteratedDeriv k f 0).re) :
    0 < ((logConcavitySequence^[m])
      (fun j => (iteratedDeriv j f 0).re / j.factorial)) k := by
  obtain ⟨p, hp, hlim⟩ := hf
  apply iterate_logConcavitySequence_pos_of_limit hp ?_ m k (div_pos hk (by positivity))
  intro j
  simpa only [Complex.div_natCast_re] using
    Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim j

/-- Every log-concavity iterate of the generalized Laguerre coefficients of
an LP function is a PF sequence at every real point. -/
theorem IsLaguerrePolya.isPolyaFreqSeq_iterate_laguerreCoefficient {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (x : ℝ) (m : ℕ) :
    IsPolyaFreqSeq ((logConcavitySequence^[m]) (laguerreCoefficient f x)) := by
  obtain ⟨p, hp, hlim⟩ := hf.exists_pf_laguerreCoefficient_approx x
  exact isPolyaFreqSeq_iterate_logConcavitySequence_of_limit hp hlim m

end RealRooted
