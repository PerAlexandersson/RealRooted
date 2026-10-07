module

public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree bounds for list sums of polynomials
-/

public section

namespace Polynomial

/-- A sum of a list of polynomials of degree at most `n` has degree at most `n`. -/
theorem natDegree_list_sum_le_of_forall_le {S : Type*} [Semiring S] {n : ℕ} :
    ∀ {l : List S[X]}, (∀ p ∈ l, p.natDegree ≤ n) → l.sum.natDegree ≤ n
  | [], _ => by simp
  | p :: l, h => by
      rw [List.sum_cons]
      exact (natDegree_add_le _ _).trans <| max_le (h p (by simp))
        (natDegree_list_sum_le_of_forall_le fun q hq ↦ h q (by simp [hq]))

end Polynomial
