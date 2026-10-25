/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluation of polynomials

`Polynomial.not_isRoot_iff_eval_ne_zero` states that `a` is not a root of `p` exactly when
`p.eval a ≠ 0`.
-/

@[expose] public section

namespace Polynomial
variable {R : Type*} [Semiring R]

lemma not_isRoot_iff_eval_ne_zero (p : R[X]) (a : R) :
    ¬ p.IsRoot a ↔ p.eval a ≠ 0 := by
  rw [Polynomial.IsRoot.def]

end Polynomial
