import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic
import Mathlib.Tactic.Ring

/-!
# Multiplicative scaling of quadratic recurrences

This division-free rescaling works over every commutative semiring, including
the zero scale.  The field-valued inverse scaling belongs in `Rescale`.
-/

namespace LinearRecurrence

variable {R : Type*} [CommSemiring R]

/-- Multiply the `n`th term of a sequence by the `n`th power of a scale. -/
def quadraticScale (s : R) (S : ℕ → R) : ℕ → R :=
  fun n ↦ s ^ n * S n

/-- Scaling a quadratic recurrence by `s` multiplies its linear and constant
coefficients by `s` and `s^2`, respectively. -/
theorem quadraticScale_isSolution {p q s : R} {S : ℕ → R}
    (hS : (quadratic p q).IsSolution S) :
    (quadratic (p * s) (q * s ^ 2)).IsSolution (quadraticScale s S) := by
  refine quadratic_isSolution_iff (p * s) (q * s ^ 2) _ |>.mpr ?_
  intro n
  unfold quadraticScale
  rw [quadratic_isSolution_iff p q S |>.mp hS n]
  ring

end LinearRecurrence
