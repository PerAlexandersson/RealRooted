import Mathlib.Algebra.MvPolynomial.Monad
import RealRooted.MultivariateStability

/-!
# Positive upper-half-plane substitutions

This is the elementary substitution step used in the finite-order Weyl-symbol
preserver.  It is the `bind₁` form of composition with polynomials whose
values have positive imaginary part on the upper half-plane.
-/

namespace RealRooted

noncomputable section

/-- Substituting upper-half-plane-valued polynomials into a stable polynomial
preserves upper-half-plane stability. -/
theorem MvUpperHalfPlaneStable.bind₁_of_im_eval_pos
    {σ τ : Type*} {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P)
    (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ i (z : τ → ℂ), (∀ j, 0 < (z j).im) →
      0 < (MvPolynomial.eval z (f i)).im) :
    MvUpperHalfPlaneStable (MvPolynomial.bind₁ f P) := by
  intro z hz hzero
  unfold MvPolynomial.eval at hzero
  rw [MvPolynomial.eval₂Hom_bind₁] at hzero
  apply hP (fun i => MvPolynomial.eval z (f i))
  · intro i
    exact hf i z hz
  · exact hzero

end

end RealRooted
