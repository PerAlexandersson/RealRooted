module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.FormalJensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IndexedProduct
import RealRooted.MultiplierSequence.JensenLimit
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Formal coefficient limits of real-rooted polynomials

A coefficientwise limit of real splitting polynomials defines an entire
Laguerre--Pólya function. No bound on the degrees or prior convergence radius is
required; zero and initial zero coefficients are allowed. This is the
coefficient-limit theorem used in Pólya's 1915 differential-operator argument.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

/-- The Jensen polynomials of the exponential Taylor data of a splitting real
polynomial also split. -/
theorem jensenPolynomial_factorial_coeff_splits {p : ℝ[X]} (hp : p.Splits) (d : ℕ) :
    (jensenPolynomial d (fun k => (k.factorial : ℝ) * p.coeff k)).Splits := by
  have hs := (isLaguerrePolya_eval_map hp).jensenPolynomial_splits d
  simpa only [iteratedDeriv_fun_eval, eval_zero_iterate_derivative, coeff_map,
    ofRealHom_eq_coe, mul_re, natCast_re, ofReal_re, natCast_im, ofReal_im,
    mul_zero, sub_zero] using hs

/-- A coefficientwise limit of real splitting polynomials defines an entire
Laguerre--Pólya function, without a degree bound or a convergence assumption. -/
theorem isLaguerrePolya_of_tendsto_coeff {p : ℕ → ℝ[X]} {a : ℕ → ℝ}
    (hp : ∀ n, (p n).Splits)
    (ha : ∀ k, Tendsto (fun n => (p n).coeff k) atTop (𝓝 (a k))) :
    IsLaguerrePolya (complexExpGeneratingFunction (fun k => (k.factorial : ℝ) * a k)) := by
  apply isLaguerrePolya_of_jensenPolynomial_splits
  intro d
  exact jensenPolynomial_splits_of_tendsto d
    (fun n => jensenPolynomial_factorial_coeff_splits (hp n) d)
    (fun k => (ha k).const_mul (k.factorial : ℝ))

end RealRooted
