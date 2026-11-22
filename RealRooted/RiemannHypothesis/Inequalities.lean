module

public import RealRooted.RiemannHypothesis
import RealRooted.Basic
import RealRooted.MultiplierSequence.JensenDerivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Inequality

/-!
# Turán inequalities and differentiation for xi Jensen polynomials

The inequalities here are consequences of Mathlib's `RiemannHypothesis`.
They do not assert the converse, nor the unconditional Turán theorem.
-/

public section

open Polynomial

namespace RealRooted

/-- The Turán inequality for normalized xi coefficients, conditional on RH. -/
theorem riemannXiCoeff_logConcave (hRH : RiemannHypothesis) (n : ℕ) :
    riemannXiCoeff n * riemannXiCoeff (n + 2) ≤ riemannXiCoeff (n + 1) ^ 2 := by
  have h := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  have hi := h.laguerre_form_nonneg 0
  simpa only [riemannXiCoeff, Complex.ofReal_zero, iteratedDeriv_succ,
    show n + 2 = (n + 1) + 1 from rfl, sub_nonneg] using hi

/-- Differentiating increases the shift and lowers the degree parameter. -/
theorem derivative_riemannXiJensenPolynomial (d n : ℕ) :
    (riemannXiJensenPolynomial (d + 1) n).derivative =
      C (d + 1 : ℝ) * riemannXiJensenPolynomial d (n + 1) := by
  simpa only [riemannXiJensenPolynomial, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using derivative_jensenPolynomial d (fun k => riemannXiCoeff (n + k))

/-- Under RH, the shifted degree-`d` Jensen polynomial weakly interlaces the
degree-`d+1` polynomial. Repeated and shared roots are allowed. -/
theorem riemannXiJensenPolynomial_shift_interl (hRH : RiemannHypothesis) (d n : ℕ) :
    Interl (riemannXiJensenPolynomial d (n + 1))
      (riemannXiJensenPolynomial (d + 1) n) := by
  simpa only [riemannXiJensenPolynomial, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using jensenPolynomial_shift_interl
      (riemannXiJensenPolynomial_splits hRH (d + 1) n)

end RealRooted
