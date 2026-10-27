/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Evaluation of polynomials and degree

`Polynomial.eval_one_eq_sum_range'` states that evaluating a polynomial at `1` gives the sum of
its coefficients over `Finset.range n` for any `n` larger than its natural degree.
-/

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
