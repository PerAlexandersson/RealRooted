module

public import RealRooted.Hermite.Poulain
public import RealRooted.SimpleRoots
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.Hermite.PoulainSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorProduct
import RealRooted.SimpleRoots.Reflection
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Simple Jensen roots for polynomial symbols

A real-rooted polynomial symbol nonzero at zero has simple Jensen roots in
every degree, including bounds exceeding its own degree. The reflected
differential image may have a multiple zero at the origin; reflection removes
it. This is the polynomial case of Craven–Csordas (1994), Proposition 4.1(1).
It does not assert strictness for arbitrary polynomial inputs.
-/

public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- The Taylor differential operator of a polynomial symbol agrees with the
finite Hermite–Poulain operator. -/
theorem taylorDifferentialOperator_polynomial (q p : ℝ[X]) :
    taylorDifferentialOperator (fun z => (q.map ofRealHom).eval z) p =
      applyAsDifferentialOperator q p := by
  rw [taylorDifferentialOperator, applyAsDifferentialOperator_eq_sum_range_right]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  simp [iteratedDeriv_fun_eval, eval_zero_iterate_derivative,
    mul_div_cancel_left₀ _ hk]

/-- The differential image of a pure power has no multiple nonzero root
when the real-rooted symbol is nonzero at zero. -/
theorem simpleExcept_zero_operator_X_pow {q : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (d : ℕ) :
    HasSimpleRootsExcept (applyAsDifferentialOperator q (X ^ d)) 0 := by
  have hF0 : applyAsDifferentialOperator q (X ^ d) ≠ 0 := by
    rw [← taylorDifferentialOperator_polynomial]
    apply taylorDifferentialOperator_ne_zero _ (pow_ne_zero d X_ne_zero)
    simpa [coeff_zero_eq_eval_zero] using hq0
  intro r hr0 hr
  have hpos := (rootMultiplicity_pos hF0).mpr hr
  by_contra hnot
  have hm : 2 ≤ (applyAsDifferentialOperator q (X ^ d)).rootMultiplicity r := by lia
  have hback := rootMultiplicity_operator_eq_add_natDegree hq hq0
    (pow_ne_zero d X_ne_zero) (Splits.X.pow d) hm
  have hmult : (X ^ d : ℝ[X]).rootMultiplicity r = 0 := by
    apply rootMultiplicity_eq_zero
    simpa only [IsRoot.def, eval_pow, eval_X] using pow_ne_zero d hr0
  lia

/-- Every Jensen polynomial of a real-rooted polynomial symbol with nonzero
constant coefficient has simple real roots, without a degree restriction. -/
theorem simple_jensenPolynomial_polynomial {q : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (d : ℕ) :
    IsSimpleRealRooted (jensenPolynomial d (fun k => (k.factorial : ℝ) * q.coeff k)) := by
  have hLP : IsLaguerrePolya (fun z => (q.map ofRealHom).eval z) := by
    apply IsLaguerrePolya.of_forall_approx
    intro R ε hε
    exact ⟨q, Or.inr hq, fun _ _ => by simpa using hε⟩
  have hgamma : (fun k => (iteratedDeriv k (fun z => (q.map ofRealHom).eval z) 0).re) =
      (fun k => (k.factorial : ℝ) * q.coeff k) := by
    funext k
    simp [iteratedDeriv_fun_eval, eval_zero_iterate_derivative]
  have hsplit := hLP.jensenPolynomial_splits d
  rw [hgamma] at hsplit
  have hsimple := simpleExcept_zero_operator_X_pow hq hq0 d
  rw [← taylorDifferentialOperator_polynomial, taylorDifferentialOperator_X_pow,
    hgamma] at hsimple
  have hconst : (jensenPolynomial d (fun k => (k.factorial : ℝ) * q.coeff k)).coeff 0 ≠ 0 := by
    simpa [coeff_jensenPolynomial] using hq0
  refine ⟨?_, hsplit, hsimple.of_reflect hconst hsplit (natDegree_jensenPolynomial_le d _)⟩
  intro hz
  exact hconst (by simp [hz])

end RealRooted
