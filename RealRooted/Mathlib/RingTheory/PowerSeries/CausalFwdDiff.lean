import RealRooted.Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Causal forward differences of power series

The causal forward difference of a coefficient sequence corresponds to
multiplication by `1 - X`.
-/

namespace PowerSeries

/-- Taking the causal forward difference of coefficients is multiplication by
`1 - X`. -/
theorem mk_causalFwdDiff {R : Type*} [Ring R] (a : ℕ → R) :
    mk (Function.causalFwdDiff a) = (1 - X) * mk a := by
  ext (_ | n)
  · simp [Function.causalFwdDiff]
  · simp [Function.causalFwdDiff, sub_mul]

/-- Iterated causal forward differences correspond to powers of `1 - X`. -/
theorem mk_causalFwdDiff_iter {R : Type*} [Ring R] (a : ℕ → R) (k : ℕ) :
    mk ((Function.causalFwdDiff^[k]) a) = (1 - X) ^ k * mk a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', mk_causalFwdDiff, ih, pow_succ', mul_assoc]

end PowerSeries
