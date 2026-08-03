import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Additional total-degree bounds

This file contains Mathlib-shaped compatibility lemmas for multivariate
polynomial degrees.
-/

open scoped BigOperators

namespace MvPolynomial

/-- Total degree is at most the sum of the coordinatewise degrees. -/
theorem totalDegree_le_sum_degreeOf {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) :
    p.totalDegree ≤ ∑ i, p.degreeOf i := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro d hd
  calc
    d.sum (fun _ e => e) = ∑ i, d i := by
      rw [Finsupp.sum_fintype]
      intro
      rfl
    _ ≤ ∑ i, p.degreeOf i :=
      Finset.sum_le_sum fun i _ => le_degreeOf_of_mem_support i hd

end MvPolynomial
