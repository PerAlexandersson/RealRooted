module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator

import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

public import RealRooted.Hermite.Poulain
public import RealRooted.SimpleRoots
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Hermite.PoulainSimple
import RealRooted.Hermite.GaussianOperator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorProduct
import RealRooted.SimpleRoots.Reflection
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Exponential–polynomial differential symbols

Multiplication by a real exponential translates the polynomial input before
applying the finite symbol. This gives the simple-root degree range for the
exceptional symbols in Craven–Csordas (1994), Proposition 4.1(2). In fact the
finite multiplicity theorem also includes degree `deg q + 1`.
-/

public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- An exponential factor translates the input to a finite differential operator. -/
theorem taylor_polynomial_exp_eq_operator (q p : ℝ[X]) (a : ℝ) :
    taylorDifferentialOperator
      (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) p =
      applyAsDifferentialOperator q (p.comp (X + C a)) := by
  rw [taylorDifferentialOperator_polynomial_mul (by fun_prop), taylor_exp_linear_eq_comp]

/-- In the finite degree range, a polynomial–exponential symbol strictly
regularizes every nonzero split polynomial input. -/
theorem simple_taylor_polynomial_exp_of_degree {q p : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (a : ℝ)
    (hp0 : p ≠ 0) (hp : p.Splits) (hd : p.natDegree - 1 ≤ q.natDegree) :
    IsSimpleRealRooted (taylorDifferentialOperator
      (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) p) := by
  rw [taylor_polynomial_exp_eq_operator]
  have hpcomp : p.comp (X + C a) ≠ 0 := by
    intro hz
    have h := congrArg (fun v : ℝ[X] => v.comp (X - C a)) hz
    exact hp0 (by simpa [comp_assoc] using h)
  apply isSimpleRealRooted_applyAsDifferentialOperator hq hq0 hpcomp (hp.comp_X_add_C a)
  simpa [natDegree_comp] using hd

/-- The Jensen polynomials of a real-rooted polynomial times a real
exponential have simple roots through degree `deg q + 1`. This contains the
degree range stated in Craven–Csordas Proposition 4.1(2). -/
theorem simple_jensen_polynomial_exp_of_degree {q : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (a : ℝ) (d : ℕ)
    (hd : d - 1 ≤ q.natDegree) :
    IsSimpleRealRooted (jensenPolynomial d (fun k =>
      (iteratedDeriv k (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re)) := by
  have hsimple := simple_taylor_polynomial_exp_of_degree hq hq0 a
    (pow_ne_zero d X_ne_zero) (Splits.X.pow d) (by simpa using hd)
  rw [taylorDifferentialOperator_X_pow] at hsimple
  have hsplit := (splits_reflect_iff (natDegree_jensenPolynomial_le d _)).mp hsimple.2.1
  have hconst : (jensenPolynomial d (fun k =>
      (iteratedDeriv k (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re)).coeff 0
        ≠ 0 := by
    simp only [coeff_jensenPolynomial, Nat.zero_le, ite_true, Nat.choose_zero_right,
      Nat.cast_one, one_mul, iteratedDeriv_zero]
    simpa [← coeff_zero_eq_eval_zero] using hq0
  refine ⟨?_, hsplit, hsimple.2.2.of_reflect hconst hsplit (natDegree_jensenPolynomial_le d _)⟩
  intro hz
  exact hconst (by simp [hz])

end RealRooted
