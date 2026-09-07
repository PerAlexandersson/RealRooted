module

public import Mathlib.Algebra.Polynomial.Eval.Degree

public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- Evaluating at one sums all coefficients in any range past the natural
degree. -/
lemma eval_one_eq_sum_range' (p : R[X]) {n : ℕ} (hdegree : p.natDegree < n) :
    p.eval 1 = ∑ k ∈ Finset.range n, p.coeff k := by
  rw [Polynomial.eval_eq_sum_range' hdegree]
  simp

end Polynomial
