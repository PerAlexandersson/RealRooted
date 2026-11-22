module

public import RealRooted.RiemannHypothesis
public import RealRooted.SimpleRoots
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.JensenSimple
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.RiemannHypothesis.Inequalities

/-!
# Simple roots of the ordinary xi Jensen polynomials

Under Mathlib's RH, every ordinary normalized xi Jensen polynomial has simple
real roots. The argument uses the order-one-half bound for every derivative of
`riemannXiTheta`, unconditional nonpolynomiality, and finite differential-symbol
multiplicity descent. It asserts nothing about simplicity of xi's own zeros.
-/

public section

open Polynomial Complex

namespace RealRooted

/-- Every derivative of the square-variable xi function is nonpolynomial,
because all its subsequent Taylor derivatives at zero are nonzero. -/
theorem iteratedDeriv_riemannXiTheta_ne_polynomial (n : ℕ) (p : ℂ[X]) :
    iteratedDeriv n riemannXiTheta ≠ fun z => p.eval z := by
  intro hp
  have h := congrArg (fun f : ℂ → ℂ => iteratedDeriv (p.natDegree + 1) f 0) hp
  rw [Polynomial.iteratedDeriv_fun_eval,
    iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree)] at h
  simp only [eval_zero] at h
  have heq : iteratedDeriv (p.natDegree + 1) (iteratedDeriv n riemannXiTheta) 0 =
      iteratedDeriv (n + (p.natDegree + 1)) riemannXiTheta 0 := by
    simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm]
  rw [heq] at h
  exact iteratedDeriv_riemannXiTheta_zero_ne_zero _ h

/-- RH implies simple real roots for every ordinary xi Jensen polynomial,
in all degrees and all coefficient shifts, including constants. -/
theorem isSimpleRealRooted_riemannXiJensenPolynomial
    (hRH : RiemannHypothesis) (d n : ℕ) :
    IsSimpleRealRooted (riemannXiJensenPolynomial d n) := by
  have hf := (riemannHypothesis_iff_isLaguerrePolya_riemannXiTheta.mp hRH).iterate_deriv n
  have hs := hf.simple_jensenPolynomial
    (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta n)
    (by norm_num) (iteratedDeriv_riemannXiTheta_zero_ne_zero n)
    (iteratedDeriv_riemannXiTheta_ne_polynomial n) d
  simpa only [riemannXiJensenPolynomial, riemannXiCoeff, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, Nat.add_comm] using hs

/-- Consecutive derivative-related xi Jensen rows have no common real root under RH. -/
theorem riemannXiJensenPolynomial_shift_no_common_root
    (hRH : RiemannHypothesis) (d n : ℕ) (r : ℝ) :
    ¬ ((riemannXiJensenPolynomial d (n + 1)).IsRoot r ∧
      (riemannXiJensenPolynomial (d + 1) n).IsRoot r) := by
  intro hr
  have hs := (isSimpleRealRooted_riemannXiJensenPolynomial hRH (d + 1) n).2.2
  apply hs.eval_derivative_ne_zero hr.2
  rw [derivative_riemannXiJensenPolynomial, eval_mul,
    show (riemannXiJensenPolynomial d (n + 1)).eval r = 0 from hr.1, mul_zero]

/-- The unshifted ordinary Jensen family is simple-real-rooted exactly under RH. -/
theorem riemannHypothesis_iff_simple_jensen_zero :
    RiemannHypothesis ↔ ∀ d, IsSimpleRealRooted (riemannXiJensenPolynomial d 0) := by
  constructor
  · intro h d
    exact isSimpleRealRooted_riemannXiJensenPolynomial h d 0
  · intro h
    exact riemannHypothesis_iff_riemannXiJensenPolynomial_zero_splits.mpr
      (fun d => (h d).2.1)

/-- RH is equivalent to simple real-rootedness in every ordinary Jensen degree and shift. -/
theorem riemannHypothesis_iff_simple_jensen :
    RiemannHypothesis ↔ ∀ d n, IsSimpleRealRooted (riemannXiJensenPolynomial d n) := by
  constructor
  · exact isSimpleRealRooted_riemannXiJensenPolynomial
  · intro h
    exact riemannHypothesis_iff_simple_jensen_zero.mpr (fun d => h d 0)

end RealRooted
