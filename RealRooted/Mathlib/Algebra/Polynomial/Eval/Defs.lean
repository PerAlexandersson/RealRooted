module

public import Mathlib.Algebra.Polynomial.Eval.Defs

public section

namespace Polynomial
variable {R : Type*} [Semiring R]

lemma not_isRoot_iff_eval_ne_zero (p : R[X]) (a : R) :
    ¬ p.IsRoot a ↔ p.eval a ≠ 0 := by
  rw [Polynomial.IsRoot.def]

end Polynomial
