module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
public import RealRooted.SimpleRoots
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Hermite.PoulainSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.PolynomialFactors
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.SimpleRoots.Reflection
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Simple Jensen roots below order one

A nonpolynomial Laguerre–Pólya symbol of order below one and nonzero at zero
strictly regularizes every nonzero real-rooted polynomial. Its Jensen
polynomials consequently have simple roots. This is a growth-restricted
instance of the corrected Craven–Csordas (1994) Proposition 4.1 argument.
-/

public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- A nonpolynomial LP symbol of order below one strictly regularizes every
nonzero real-rooted polynomial through its Taylor differential operator. -/
theorem IsLaguerrePolya.simple_taylorDifferentialOperator {f : ℂ → ℂ} {rho : ℝ}
    (hf : IsLaguerrePolya f) (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hf0 : f 0 ≠ 0) (hnp : ∀ q : ℂ[X], f ≠ fun z => q.eval z)
    {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits) :
    IsSimpleRealRooted (taylorDifferentialOperator f p) := by
  have hfn : f ≠ 0 := fun h => hf0 (by simp [h])
  obtain ⟨q, g, hq, hq0, hdegree, hg, hg0, hfactor⟩ :=
    exists_polynomial_factor_of_order_lt_one horder hrho hf.differentiable hf0 hf.conj
      (fun z hz => hf.im_eq_zero_of_eq_zero hfn hz) hnp (p.natDegree - 1)
  have hgre : (g 0).re ≠ 0 := by
    intro hz
    have hreal := ofReal_re_iteratedDeriv_zero hg.conj 0
    simp only [iteratedDeriv_zero, hz, ofReal_zero] at hreal
    exact hg0 hreal.symm
  rw [show f = (fun z => (q.map ofRealHom).eval z * g z) from funext hfactor,
    taylorDifferentialOperator_polynomial_mul hg.differentiable]
  apply isSimpleRealRooted_applyAsDifferentialOperator hq hq0
    (taylorDifferentialOperator_ne_zero hgre hp0) (hg.taylorDifferentialOperator_splits hp)
  rwa [natDegree_taylorDifferentialOperator hgre hp0]

/-- Every Jensen polynomial of a nonpolynomial LP symbol of order below one
and nonzero initial coefficient has simple real roots. The final coefficient
may vanish, so no exact-degree hypothesis is imposed. -/
theorem IsLaguerrePolya.simple_jensenPolynomial {f : ℂ → ℂ} {rho : ℝ}
    (hf : IsLaguerrePolya f) (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hf0 : f 0 ≠ 0) (hnp : ∀ q : ℂ[X], f ≠ fun z => q.eval z) (d : ℕ) :
    IsSimpleRealRooted (jensenPolynomial d (fun k => (iteratedDeriv k f 0).re)) := by
  have hsimple := hf.simple_taylorDifferentialOperator horder hrho hf0 hnp
    (pow_ne_zero d X_ne_zero) (Splits.X.pow d)
  rw [taylorDifferentialOperator_X_pow] at hsimple
  have hconst : (jensenPolynomial d (fun k => (iteratedDeriv k f 0).re)).coeff 0 ≠ 0 := by
    simp only [coeff_jensenPolynomial, Nat.zero_le, ite_true, Nat.choose_zero_right,
      Nat.cast_one, one_mul, iteratedDeriv_zero]
    intro hz
    have hreal := ofReal_re_iteratedDeriv_zero hf.conj 0
    simp only [iteratedDeriv_zero, hz, ofReal_zero] at hreal
    exact hf0 hreal.symm
  refine ⟨?_, hf.jensenPolynomial_splits d,
    hsimple.2.2.of_reflect hconst (hf.jensenPolynomial_splits d)
      (natDegree_jensenPolynomial_le d _)⟩
  intro hz
  exact hconst (by simp [hz])

end RealRooted
