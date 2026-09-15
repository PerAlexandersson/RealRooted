import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Evaluation away from the variables of a multivariate polynomial

This file supplies a small compatibility lemma saying that evaluation is
unchanged when an assignment is modified outside the polynomial's variables.
-/

namespace MvPolynomial

/-- Updating an assignment outside a polynomial's variables does not change
its evaluation. -/
theorem eval_update_eq_of_notMem_vars
    {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    {P : MvPolynomial σ R} {k : σ} (hk : k ∉ P.vars)
    (x : σ → R) (t : R) :
    eval (Function.update x k t) P = eval x P := by
  apply eval₂_congr
  intro i d hid hd
  have hi : i ∈ P.vars :=
    mem_vars_iff_mem_support i |>.2 ⟨d, mem_support_iff.2 hd, hid⟩
  have hik : i ≠ k := by
    intro h
    subst i
    exact hk hi
  simp [hik]

end MvPolynomial
