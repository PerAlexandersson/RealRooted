module

public import RealRooted.PFPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Expand

/-!
# The generating polynomial of the generalized Laguerre forms

For a real splitting polynomial `p`, the product `p(x + i t) p(x - i t)` is an
even polynomial in `t`. Its polynomial in `t²` has roots `-(x - r)²`, where `r`
ranges over the roots of `p`, with multiplicity. In particular it is a PF polynomial.
-/

@[expose] public section

open Polynomial Complex

noncomputable section

namespace RealRooted

/-- The polynomial whose coefficients are the generalized Laguerre forms of a
real splitting polynomial at `x`. -/
def laguerreGeneratingPolynomial (p : ℝ[X]) (x : ℝ) : ℝ[X] :=
  C (p.leadingCoeff ^ 2) *
    (p.roots.map fun r => X + C ((x - r) ^ 2)).prod

/-- The generating polynomial of the generalized Laguerre forms is PF, including
the zero-polynomial case. -/
theorem isPFPolynomial_laguerreGeneratingPolynomial (p : ℝ[X]) (x : ℝ) :
    IsPFPolynomial (laguerreGeneratingPolynomial p x) := by
  apply (IsPFPolynomial.of_C_nonneg (sq_nonneg p.leadingCoeff)).mul
  induction p.roots using Multiset.induction_on with
  | empty => simpa using IsPFPolynomial.one
  | cons r s ih =>
    simpa using (isPFPolynomial_X_add_C (sq_nonneg (x - r))).mul ih

private theorem eval_prod_squared_factors (s : Multiset ℝ) (x : ℝ) (z : ℂ) :
    (((s.map fun r => (X + C ((x - r) ^ 2) : ℝ[X])).prod).map ofRealHom).eval (z ^ 2) =
      (((s.map fun r => (X - C r : ℝ[X])).prod).map ofRealHom).eval (x + z * I) *
        (((s.map fun r => (X - C r : ℝ[X])).prod).map ofRealHom).eval (x - z * I) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, eval_mul,
      Polynomial.map_add, Polynomial.map_sub, map_X, map_C, eval_add, eval_sub, eval_X,
      eval_C, ofRealHom_eq_coe]
    rw [ih]
    push_cast
    ring_nf
    simp [I_sq]

/-- The square substitution of the generating polynomial is the product along
the two imaginary directions. -/
theorem eval_laguerreGeneratingPolynomial {p : ℝ[X]} (hp : p.Splits) (x : ℝ) (z : ℂ) :
    ((laguerreGeneratingPolynomial p x).map ofRealHom).eval (z ^ 2) =
      (p.map ofRealHom).eval (x + z * I) * (p.map ofRealHom).eval (x - z * I) := by
  conv_rhs => rw [hp.eq_prod_roots]
  simp only [laguerreGeneratingPolynomial, Polynomial.map_mul, map_C, eval_mul, eval_C,
    ofRealHom_eq_coe, ofReal_pow, eval_prod_squared_factors]
  ring

end RealRooted
