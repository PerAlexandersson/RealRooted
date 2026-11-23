/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic.TypeStar

/-!
# Finite Taylor evaluation in Hasse and ordinary derivatives
-/

public section

namespace Polynomial

/-- Taylor evaluation as a finite sum of Hasse derivative values. -/
theorem eval_add_eq_sum_hasseDeriv {R : Type*} [CommSemiring R]
    (p : R[X]) (x y : R) :
    p.eval (x + y) = ∑ k ∈ Finset.range (p.natDegree + 1),
      (hasseDeriv k p).eval x * y ^ k := by
  rw [add_comm x y, ← taylor_eval x p y, eval_eq_sum_range]
  simp only [natDegree_taylor, taylor_coeff]

/-- Over a characteristic-zero field, a Hasse derivative value is the ordinary
iterated derivative value divided by the corresponding factorial. -/
theorem eval_hasseDeriv_eq_div_factorial {K : Type*} [Field K] [CharZero K]
    (p : K[X]) (x : K) (k : ℕ) :
    (hasseDeriv k p).eval x = (derivative^[k] p).eval x / k.factorial := by
  have hpoly : derivative^[k] p = k.factorial • hasseDeriv k p := by
    rw [← factorial_smul_hasseDeriv]
    rfl
  rw [hpoly, eval_smul, nsmul_eq_mul]
  exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr k.factorial_ne_zero)).symm

end Polynomial
