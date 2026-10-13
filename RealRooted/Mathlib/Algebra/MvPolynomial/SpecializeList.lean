import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize

/-!
# Ordered specialization as one substitution

This file identifies iterated scalar specialization with a single
multivariate-polynomial substitution.
-/

namespace MvPolynomial

/-- Ordered scalar specialization along a list is a single substitution. -/
theorem specializeAtList_eq_aeval {σ R : Type*} [CommSemiring R]
    [DecidableEq σ] (c : σ → R) (l : List σ) (P : MvPolynomial σ R) :
    specializeAtList c l P =
      aeval (fun u => if u ∈ l then C (c u) else X u) P := by
  induction l generalizing P with
  | nil => exact (aeval_X_left_apply P).symm
  | cons i l ih =>
      rw [specializeAtList_cons, ih, specializeAt]
      rw [← AlgHom.comp_apply, comp_aeval]
      congr 2
      funext u
      by_cases hu : u = i
      · subst hu
        simp
      · simp [hu]

end MvPolynomial
