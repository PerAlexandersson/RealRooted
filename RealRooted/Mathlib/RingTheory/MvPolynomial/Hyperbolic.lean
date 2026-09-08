import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Hyperbolic multivariate polynomials

This file contains definitions intended for upstreaming to
`Mathlib.RingTheory.MvPolynomial.Hyperbolic`.
-/

open Polynomial

namespace MvPolynomial

noncomputable section

/-- Restrict a multivariate polynomial to the affine line `x + t e`. -/
def affineLineRestriction {σ R : Type*} [CommSemiring R]
    (x e : σ → R) (P : MvPolynomial σ R) : R[X] :=
  eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (e i) * Polynomial.X) P

@[simp] theorem eval_affineLineRestriction
    {σ R : Type*} [CommSemiring R] (x e : σ → R)
    (P : MvPolynomial σ R) (t : R) :
    (affineLineRestriction x e P).eval t =
      MvPolynomial.eval (fun i => x i + e i * t) P := by
  unfold affineLineRestriction
  change Polynomial.evalRingHom t
      (eval₂Hom Polynomial.C
        (fun i => Polynomial.C (x i) + Polynomial.C (e i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id R := by
    ext c
    simp
  rw [hC]
  rfl

/-- A polynomial is hyperbolic at `e` when it does not vanish there and every
affine-line restriction in direction `e` splits over the coefficient semiring.
For the standard notion, use this predicate with a homogeneity hypothesis. -/
def HyperbolicAt {σ R : Type*} [CommSemiring R]
    (P : MvPolynomial σ R) (e : σ → R) : Prop :=
  MvPolynomial.eval e P ≠ 0 ∧
    ∀ x : σ → R, (affineLineRestriction x e P).Splits

end

end MvPolynomial
