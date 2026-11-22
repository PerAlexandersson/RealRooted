module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Differential-operator criterion for the Laguerre--Pólya class

A real entire function belongs to the Laguerre--Pólya class exactly when its
Taylor differential operator preserves real-rootedness. Testing on monomials
already suffices by Jensen's criterion.
-/

public section

open Polynomial Complex
open scoped ComplexConjugate

namespace RealRooted

/-- A real entire function is Laguerre--Pólya exactly when its Taylor
differential operator preserves splitting over the reals. -/
theorem isLaguerrePolya_iff_taylorDifferentialOperator_splits {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hconj : ∀ z, f (conj z) = conj (f z)) :
    IsLaguerrePolya f ↔
      ∀ p : ℝ[X], p.Splits → (taylorDifferentialOperator f p).Splits := by
  constructor
  · exact fun h _ hp => h.taylorDifferentialOperator_splits hp
  · intro h
    apply (isLaguerrePolya_iff_jensenPolynomial_splits hf
      (fun k => (ofReal_re_iteratedDeriv_zero hconj k).symm)).mpr
    intro d
    apply (splits_reflect_iff (natDegree_jensenPolynomial_le d _)).mp
    rw [← taylorDifferentialOperator_X_pow]
    exact h _ (Splits.X.pow d)

end RealRooted
