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

/-- A global condition on evaluations can be checked after fixing two
coordinates that do not occur in the polynomial. -/
theorem forall_eval_iff_forall_eval_update_update_of_notMem_vars
    {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    {P : MvPolynomial σ R} {i j : σ}
    (hi : i ∉ P.vars) (hj : j ∉ P.vars) (s t : R) (q : R → Prop) :
    (∀ x, q (eval x P)) ↔
      ∀ x, q (eval (Function.update (Function.update x i s) j t) P) := by
  simp only [eval_update_eq_of_notMem_vars hi,
    eval_update_eq_of_notMem_vars hj]

end MvPolynomial
