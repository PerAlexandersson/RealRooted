/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Taylor shifts and derivatives

The Taylor shift `taylor r p = p.comp (X + C r)` commutes with the formal derivative.
-/

public section

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- The Taylor shift commutes with the derivative. -/
theorem taylor_derivative (r : R) (p : R[X]) :
    taylor r (derivative p) = derivative (taylor r p) := by
  simp [taylor_apply, derivative_comp]

/-- The Taylor shift commutes with iterated derivatives. -/
theorem taylor_iterate_derivative (r : R) (p : R[X]) (n : ℕ) :
    taylor r (derivative^[n] p) = derivative^[n] (taylor r p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih, taylor_derivative]

end Polynomial
