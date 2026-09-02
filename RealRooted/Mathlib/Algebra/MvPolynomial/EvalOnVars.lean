import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Evaluation on the variable support

This file contains a Mathlib-shaped evaluation lemma for multivariate
polynomials.
-/

namespace MvPolynomial

/-- Multivariate evaluation depends only on the coordinates occurring in the
polynomial's variable support. -/
theorem eval_eq_of_eq_on_vars {sigma R : Type*} [CommSemiring R]
    (P : MvPolynomial sigma R) (x y : sigma → R)
    (hxy : ∀ i ∈ P.vars, x i = y i) :
    eval x P = eval y P :=
  eval₂Hom_congr' rfl (fun i hi _ ↦ hxy i hi) rfl

end MvPolynomial
