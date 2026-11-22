module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.LaguerreInequalities.Analytic
public import RealRooted.BrandenLC.Sequence
import RealRooted.RiemannHypothesis
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogConcavity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

/-!
# Infinite log-concavity consequences of the Riemann hypothesis

Under Mathlib's RH, every log-concavity iterate of each ordinary xi Taylor
sequence is PF. All entries and all Toeplitz minors of every iterate are
therefore nonnegative. The factorial normalization is essential: these are
ordinary coefficients `γ(n+k)/k!`, not the raw exponential Taylor data.

The generalized Laguerre coefficients of every xi derivative have the same
iterated PF property at every real point. These consequences follow from
Brändén's finite preservation theorem and the checked LP approximation results.
-/

public section

namespace RealRooted

/-- RH implies the PF property after every log-concavity iterate of every
ordinary xi Taylor sequence. -/
theorem isPolyaFreqSeq_iterate_logConcavity_riemannXiCoeff
    (hRH : RiemannHypothesis) (n m : ℕ) :
    IsPolyaFreqSeq ((logConcavitySequence^[m])
      (fun k => riemannXiCoeff (n + k) / k.factorial)) := by
  have hf := isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n
  have h := hf.isPolyaFreqSeq_iterate_logConcavity m
  simpa only [riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using h

/-- Every entry of every log-concavity iterate of the normalized ordinary
xi coefficients is nonnegative under RH. -/
theorem iterate_logConcavity_riemannXiCoeff_nonneg
    (hRH : RiemannHypothesis) (n m k : ℕ) :
    0 ≤ ((logConcavitySequence^[m])
      (fun j => riemannXiCoeff (n + j) / j.factorial)) k :=
  (isPolyaFreqSeq_iterate_logConcavity_riemannXiCoeff hRH n m).nonneg k

/-- Under RH the ordinary xi coefficient sequences are strictly infinitely
log-concave: every entry of every iterate is positive. -/
theorem iterate_logConcavity_riemannXiCoeff_pos
    (hRH : RiemannHypothesis) (n m k : ℕ) :
    0 < ((logConcavitySequence^[m])
      (fun j => riemannXiCoeff (n + j) / j.factorial)) k := by
  have hf := isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n
  have hk : 0 < (iteratedDeriv k (iteratedDeriv n riemannXiTheta) 0).re := by
    simpa only [riemannXiCoeff, iteratedDeriv_eq_iterate,
      ← Function.iterate_add_apply, Nat.add_comm] using riemannXiCoeff_pos (n + k)
  simpa only [riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using hf.iterate_logConcavity_pos m k hk

/-- RH gives iterated PF inequalities for the generalized Laguerre sequence
of every xi derivative at every real point. -/
theorem isPolyaFreqSeq_iterate_laguerreCoefficient_riemannXiTheta
    (hRH : RiemannHypothesis) (n m : ℕ) (x : ℝ) :
    IsPolyaFreqSeq ((logConcavitySequence^[m])
      (laguerreCoefficient (iteratedDeriv n riemannXiTheta) x)) := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  exact hf.isPolyaFreqSeq_iterate_laguerreCoefficient x m

end RealRooted
