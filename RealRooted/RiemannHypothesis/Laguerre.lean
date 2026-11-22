module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.MultiplierSequence.JensenLaguerre
import RealRooted.RiemannHypothesis
import RealRooted.MultiplierSequence.JensenLaguerreLimit

/-!
# Laguerre Jensen criteria for the Riemann hypothesis

Mathlib's RH is equivalent to splitting of all Laguerre transforms of the
normalized xi coefficients, for every parameter at least `-2`. The unshifted
family suffices. The rising-factorial normalization includes both exceptional
parameters `-1` and `-2` without Gamma quotients.

## References

* Cormac O'Sullivan, *Zeros of Jensen polynomials and asymptotics for the Riemann
  xi function*, Theorem 3.9, https://arxiv.org/abs/2007.13582.
-/

public section

open Polynomial

namespace RealRooted

/-- Under Mathlib's RH, every shifted xi Laguerre Jensen polynomial splits
throughout the extended parameter range. -/
theorem laguerreJensenPolynomial_riemannXiCoeff_splits
    (hRH : RiemannHypothesis) (d n : ℕ) {alpha : ℝ} (halpha : -2 ≤ alpha) :
    (laguerreJensenPolynomial d (fun k => riemannXiCoeff (n + k)) alpha).Splits :=
  laguerreJensenPolynomial_splits (riemannXiJensenPolynomial_splits hRH d n) halpha

/-- The unshifted Laguerre Jensen family already characterizes Mathlib's RH. -/
theorem riemannHypothesis_iff_laguerreJensenPolynomial_splits :
    RiemannHypothesis ↔ ∀ d (alpha : ℝ), -2 ≤ alpha →
      (laguerreJensenPolynomial d riemannXiCoeff alpha).Splits := by
  rw [riemannHypothesis_iff_riemannXiJensenPolynomial_zero_splits]
  simp only [riemannXiJensenPolynomial, Nat.zero_add,
    jensenPolynomial_splits_iff_laguerreJensenPolynomial]

/-- All degrees, shifts, and parameters in the extended Laguerre range give
an equivalent polynomial criterion for Mathlib's RH. -/
theorem riemannHypothesis_iff_laguerreJensenPolynomial_shift_splits :
    RiemannHypothesis ↔ ∀ d n (alpha : ℝ), -2 ≤ alpha →
      (laguerreJensenPolynomial d (fun k => riemannXiCoeff (n + k)) alpha).Splits := by
  constructor
  · intro h d n alpha halpha
    exact laguerreJensenPolynomial_riemannXiCoeff_splits h d n halpha
  · intro h
    apply riemannHypothesis_iff_laguerreJensenPolynomial_splits.mpr
    intro d alpha halpha
    simpa only [Nat.zero_add] using h d 0 alpha halpha

end RealRooted
