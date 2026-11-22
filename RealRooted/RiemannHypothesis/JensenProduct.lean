module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.MultiplierSequence.JensenProduct
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.RiemannHypothesis
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Product
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.JensenProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Auxiliary Jensen criteria for the Riemann hypothesis

Any fixed nonzero Laguerre--Pólya function supplies a Jensen-product criterion
for RH. The auxiliary is allowed to vanish at the origin, so the statement
includes sine and Bessel examples with zero constant coefficient.

This is the xi specialization of O'Sullivan's Theorem 3.5,
*Zeros of Jensen polynomials and asymptotics for the Riemann xi function*,
https://arxiv.org/abs/2007.13582.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, convolving any shifted xi Taylor sequence with the Taylor data
of a Laguerre--Pólya auxiliary gives splitting Jensen polynomials. -/
theorem jensenProductPolynomial_riemannXiCoeff_splits (hRH : RiemannHypothesis)
    {g : ℂ → ℂ} {delta : ℕ → ℝ} (hg : IsLaguerrePolya g)
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) (d n : ℕ) :
    (jensenProductPolynomial d (fun k => riemannXiCoeff (n + k)) delta).Splits := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  apply (isLaguerrePolya_mul_iff_jensenProductPolynomial_splits hf.differentiable
    hg.differentiable ?_ hdelta).mp (hf.mul hg) d
  intro k
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm]
    using (ofReal_riemannXiCoeff (n + k)).symm

/-- A fixed nonzero Laguerre--Pólya auxiliary gives an unshifted Jensen-product
criterion for RH, even when that auxiliary vanishes at the origin. -/
theorem riemannHypothesis_iff_jensenProductPolynomial_splits
    {g : ℂ → ℂ} {delta : ℕ → ℝ} (hg : IsLaguerrePolya g) (hg0 : g ≠ 0)
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) :
    RiemannHypothesis ↔ ∀ d, (jensenProductPolynomial d riemannXiCoeff delta).Splits := by
  rw [riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta,
    ← isLaguerrePolya_mul_iff_of_orderLE_one orderLE_riemannXiTheta
      differentiable_riemannXiTheta riemannXiTheta_zero_ne_zero riemannXiTheta_conj hg hg0]
  exact isLaguerrePolya_mul_iff_jensenProductPolynomial_splits
    differentiable_riemannXiTheta hg.differentiable
    (fun k => (ofReal_riemannXiCoeff k).symm) hdelta

/-- The full family of shifted Jensen products for any fixed nonzero
Laguerre--Pólya auxiliary characterizes RH. -/
theorem riemannHypothesis_iff_jensenProductPolynomial_shift_splits
    {g : ℂ → ℂ} {delta : ℕ → ℝ} (hg : IsLaguerrePolya g) (hg0 : g ≠ 0)
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) :
    RiemannHypothesis ↔ ∀ d n,
      (jensenProductPolynomial d (fun k => riemannXiCoeff (n + k)) delta).Splits := by
  constructor
  · exact fun h => jensenProductPolynomial_riemannXiCoeff_splits h hg hdelta
  · intro h
    apply (riemannHypothesis_iff_jensenProductPolynomial_splits hg hg0 hdelta).mpr
    simpa using fun d => h d 0

end RealRooted
