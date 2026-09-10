import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Partial derivatives of squarefree monomials
-/

open scoped BigOperators

namespace MvPolynomial

/-- Differentiate a squarefree monomial presented as a finite product of
variables. -/
theorem pderiv_finsetProd_X {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    (x : σ) (t : Finset σ) :
    pderiv x (∏ y ∈ t, X y : MvPolynomial σ R) =
      if x ∈ t then ∏ y ∈ t.erase x, X y else 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      by_cases hax : a = x
      · subst a
        simp [ha, ih]
      · have hxa : x ≠ a := Ne.symm hax
        by_cases hxt : x ∈ t
        · simp only [Finset.prod_insert ha, pderiv_mul,
            pderiv_X_of_ne hax, ih, hxt, if_pos, zero_mul,
            zero_add, Finset.mem_insert, hxa]
          split
          · have haerase : a ∉ t.erase x :=
              fun h => ha (Finset.erase_subset x t h)
            rw [Finset.erase_insert_of_ne hax, Finset.prod_insert haerase]
          · rename_i h
            exact (h (Or.inr trivial)).elim
        · simp [ha, hax, hxa, hxt, ih]

open scoped Classical in
/-- The partial derivative of a possibly noninjective renaming is the sum of
the renamed partial derivatives over the corresponding source fiber. -/
theorem pderiv_rename_eq_sum_fiber {R σ τ : Type*} [CommSemiring R] [Fintype σ]
    (f : σ → τ) (j : τ) (P : MvPolynomial σ R) :
    pderiv j (rename f P) =
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), rename f (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, Finset.sum_add_distrib]
  | mul_X P x hP =>
      simp only [map_mul, rename_X, pderiv_mul, hP, map_add, pderiv_X,
        Pi.single_apply]
      by_cases hx : f x = j <;>
        simp [hx, Finset.sum_add_distrib, Finset.sum_mul]

end MvPolynomial
