/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.MomentTranslation
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentShift

/-!
# The shift recurrence for translated moments
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Multiplication by the translated variable gives the next translated moment. -/
theorem momentTranslate_succ (c : R) (m : ℕ → R) (n : ℕ) :
    momentTranslate c m (n + 1) =
      c * momentTranslate c m n + momentTranslate c (fun k => m (k + 1)) n := by
  simp only [momentTranslate, taylor_X_pow]
  rw [momentFunctional_shift, pow_succ', add_mul, momentFunctional_add,
    momentFunctional_C_mul, add_comm]

end Polynomial
