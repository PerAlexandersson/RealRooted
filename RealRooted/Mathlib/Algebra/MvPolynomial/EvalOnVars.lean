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

/-- A left sum index does not occur after renaming along the right inclusion. -/
theorem inl_notMem_vars_rename_inr
    {R sigma tau : Type*} [CommSemiring R] (i : sigma)
    (P : MvPolynomial tau R) :
    Sum.inl i ∉ (rename Sum.inr P).vars := by
  intro h
  obtain ⟨j, _, hji⟩ := mem_vars_rename Sum.inr P h
  exact Sum.inr_ne_inl hji

/-- A right sum index does not occur after renaming along the left inclusion. -/
theorem inr_notMem_vars_rename_inl
    {R sigma tau : Type*} [CommSemiring R] (j : tau)
    (P : MvPolynomial sigma R) :
    Sum.inr j ∉ (rename Sum.inl P).vars := by
  intro h
  obtain ⟨i, _, hij⟩ := mem_vars_rename Sum.inl P h
  exact Sum.inl_ne_inr hij

end MvPolynomial
