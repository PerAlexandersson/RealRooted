module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
public import RealRooted.SimpleRoots
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteZeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Hermite.PoulainSimple
import RealRooted.SimpleRoots.Reflection
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Strict differential operators from infinitely many LP zeros

Infinitely many real zeros provide arbitrarily long finite differential
factors. Multiplicity descent then makes every nonzero real-rooted polynomial
input simple. This proves the infinite-zero case of the strict operator
argument of Craven–Csordas (1994), without a growth assumption.
-/

public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- An LP symbol with infinitely many distinct real zeros and nonzero value
at zero makes every nonzero real-rooted polynomial input simple-real-rooted. -/
theorem IsLaguerrePolya.simple_operator_of_infinite_zeros {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hinf : Set.Infinite {r : ℝ | f r = 0})
    {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits) :
    IsSimpleRealRooted (taylorDifferentialOperator f p) := by
  obtain ⟨q, g, hq, hq0, hdegree, hg, hg0, hfactor⟩ :=
    hf.exists_polynomial_factor_of_infinite_zeros hf0 hinf (p.natDegree - 1)
  have hgre : (g 0).re ≠ 0 := by
    intro hz
    have hreal := ofReal_re_iteratedDeriv_zero hg.conj 0
    simp only [iteratedDeriv_zero, hz, ofReal_zero] at hreal
    exact hg0 hreal.symm
  rw [show f = (fun z => (q.map ofRealHom).eval z * g z) from funext hfactor,
    taylorDifferentialOperator_polynomial_mul hg.differentiable]
  apply isSimpleRealRooted_applyAsDifferentialOperator hq hq0
    (taylorDifferentialOperator_ne_zero hgre hp0) (hg.taylorDifferentialOperator_splits hp)
  rw [natDegree_taylorDifferentialOperator hgre hp0, hdegree]

/-- All Jensen polynomials of an LP symbol with infinitely many distinct
real zeros are simple when its initial coefficient is nonzero. -/
theorem IsLaguerrePolya.simple_jensen_of_infinite_zeros {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    (hinf : Set.Infinite {r : ℝ | f r = 0}) (d : ℕ) :
    IsSimpleRealRooted (jensenPolynomial d (fun k => (iteratedDeriv k f 0).re)) := by
  have hsimple := hf.simple_operator_of_infinite_zeros hf0 hinf
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
