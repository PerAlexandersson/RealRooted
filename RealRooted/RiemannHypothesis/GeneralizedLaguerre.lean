module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.AissenSchoenbergWhitneyBase
public import RealRooted.LaguerreInequalities.Analytic
import RealRooted.RiemannHypothesis
import RealRooted.LaguerreInequalities.DerivativeFormula
import RealRooted.LaguerreInequalities.RealZeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# Generalized Laguerre criteria for the Riemann hypothesis

Mathlib's RH is equivalent to all generalized Laguerre inequalities for the
square-variable xi function. Under RH, at every real point and every derivative
shift, these coefficients form a Pólya-frequency sequence.
-/

public section

open Complex

namespace RealRooted

/-- RH gives total positivity of the generalized Laguerre coefficients of
every derivative of the square-variable xi function. -/
theorem isPolyaFreqSeq_laguerreCoefficient_riemannXiTheta
    (hRH : RiemannHypothesis) (n : ℕ) (x : ℝ) :
    IsPolyaFreqSeq (laguerreCoefficient (iteratedDeriv n riemannXiTheta) x) := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  exact hf.isPolyaFreqSeq_laguerreCoefficient x

/-- Under RH every generalized Laguerre inequality holds at every real point
for every derivative of the square-variable xi function. -/
theorem laguerreCoefficient_riemannXiTheta_nonneg
    (hRH : RiemannHypothesis) (n k : ℕ) (x : ℝ) :
    0 ≤ laguerreCoefficient (iteratedDeriv n riemannXiTheta) x k :=
  (isPolyaFreqSeq_laguerreCoefficient_riemannXiTheta hRH n x).nonneg k

/-- All generalized Laguerre inequalities for the square-variable xi function
are equivalent to Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_iff_laguerreCoefficient_nonneg :
    RiemannHypothesis ↔ ∀ x k, 0 ≤ laguerreCoefficient riemannXiTheta x k := by
  constructor
  · intro h x k
    simpa only [iteratedDeriv_zero] using laguerreCoefficient_riemannXiTheta_nonneg h 0 k x
  · intro h
    apply riemannHypothesis_iff_riemannXiTheta_zeros.mpr
    exact fun _ hz => im_eq_zero_of_laguerreCoefficient_nonneg
      differentiable_riemannXiTheta riemannXiTheta_conj
      (fun hzero => riemannXiTheta_zero_ne_zero (congrFun hzero 0)) h hz

/-- The derivative-shifted generalized Laguerre inequalities give the same
criterion for Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_iff_laguerreCoefficient_shift_nonneg :
    RiemannHypothesis ↔
      ∀ n x k, 0 ≤ laguerreCoefficient (iteratedDeriv n riemannXiTheta) x k := by
  constructor
  · exact fun h n x k => laguerreCoefficient_riemannXiTheta_nonneg h n k x
  · intro h
    exact riemannHypothesis_iff_laguerreCoefficient_nonneg.mpr (by simpa using h 0)

/-- Total positivity of the generalized Laguerre coefficients at all real
points is another criterion for Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_iff_isPolyaFreqSeq_laguerreCoefficient :
    RiemannHypothesis ↔ ∀ x, IsPolyaFreqSeq (laguerreCoefficient riemannXiTheta x) := by
  constructor
  · intro h x
    simpa only [iteratedDeriv_zero] using
      isPolyaFreqSeq_laguerreCoefficient_riemannXiTheta h 0 x
  · intro h
    exact riemannHypothesis_iff_laguerreCoefficient_nonneg.mpr fun x k => (h x).nonneg k

/-- The generalized Laguerre inequalities at zero give alternating binomial
inequalities for every shift of the normalized xi coefficients. -/
theorem riemannXiCoeff_generalized_laguerre_nonneg
    (hRH : RiemannHypothesis) (n k : ℕ) :
    0 ≤ (∑ j ∈ Finset.range (2 * k + 1),
      (-1 : ℝ) ^ (j + k) * (2 * k).choose j *
        riemannXiCoeff (n + j) * riemannXiCoeff (n + (2 * k - j))) / (2 * k).factorial := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  have h := laguerreCoefficient_riemannXiTheta_nonneg hRH n k 0
  rw [laguerreCoefficient_eq_sum hf.differentiable hf.conj] at h
  simpa only [riemannXiCoeff, ofReal_zero, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using h

end RealRooted
