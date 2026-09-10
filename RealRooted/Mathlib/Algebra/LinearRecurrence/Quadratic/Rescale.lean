import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic
import Mathlib.Tactic.FieldSimp

/-!
# Rescaling quadratic recurrences

This algebraic normalization rescales a quadratic recurrence by a nonzero
field element. Choosing square roots or proving real analytic bounds belongs
to separate clients.
-/

namespace LinearRecurrence

variable {K : Type*} [Field K]

/-- Divide the `n`th term of a sequence by the `n`th power of a scale. -/
def quadraticRescale (s : K) (S : ℕ → K) : ℕ → K :=
  fun n ↦ S n / s ^ n

/-- Rescaling by `s` divides the linear and constant recurrence coefficients
by `s` and `s^2`, respectively. -/
theorem quadraticRescale_isSolution {p q s : K} {S : ℕ → K} (hs : s ≠ 0)
    (hS : (quadratic p q).IsSolution S) :
    (quadratic (p / s) (q / s ^ 2)).IsSolution (quadraticRescale s S) := by
  refine quadratic_isSolution_iff (p / s) (q / s ^ 2) _ |>.mpr ?_
  intro n
  unfold quadraticRescale
  rw [quadratic_isSolution_iff p q S |>.mp hS n]
  field_simp [pow_succ, hs]
  ring

end LinearRecurrence
