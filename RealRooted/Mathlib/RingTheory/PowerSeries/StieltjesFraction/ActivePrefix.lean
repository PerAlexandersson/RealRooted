/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Uniqueness

/-!
# Equality of Stieltjes fractions on their active prefixes

The first zero numerator belongs to the active prefix. Every coefficient
after it is irrelevant to the formal fraction. In particular an existential
tail parametrization must not be imposed on a standardized zero tail.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Agreement up to a terminating numerator, including that zero, gives the
same formal fraction regardless of the remaining tails. -/
theorem stieltjesTail_eq_of_terminating_prefix {a b : ℕ → R} {N : ℕ}
    (ha : a N = 0) (hab : ∀ k ≤ N, a k = b k) :
    stieltjesTail a 0 = stieltjesTail b 0 := by
  have hb : b N = 0 := (hab N le_rfl).symm.trans ha
  rw [stieltjesTail_eq_convergent_of_zero a N 0 (by simpa using ha),
    stieltjesTail_eq_convergent_of_zero b N 0 (by simpa using hb)]
  exact stieltjesConvergent_eq_of_prefix N 0 0 fun i hi => by
    simpa only [Nat.zero_add] using hab i hi.le

/-- Agreement at every active numerator is sufficient for equality of formal fractions. -/
theorem stieltjesTail_eq_of_active_prefix {a b : ℕ → R}
    (hab : ∀ n, (∀ k < n, a k ≠ 0) → a n = b n) :
    stieltjesTail a 0 = stieltjesTail b 0 := by
  classical
  by_cases hz : ∃ n, a n = 0
  · let N := Nat.find hz
    have hN : a N = 0 := Nat.find_spec hz
    apply stieltjesTail_eq_of_terminating_prefix hN
    intro k hk
    apply hab k
    intro j hj
    exact Nat.find_min hz (hj.trans_le hk)
  · push Not at hz
    have heq : a = b := funext fun n => hab n (fun k _ => hz k)
    rw [heq]

/-- Equality of normalized fractions is exactly agreement through the first zero.
This is the active-prefix form of the usual uniqueness theorem. -/
theorem stieltjesTail_eq_iff_active_prefix [IsDomain R] {a b : ℕ → R} :
    stieltjesTail a 0 = stieltjesTail b 0 ↔
      ∀ n, (∀ k < n, a k ≠ 0) → a n = b n := by
  constructor
  · intro h n hn
    simpa only [Nat.zero_add] using
      eq_of_stieltjesTail_eq_of_prefix_ne_zero n h (by simpa using hn)
  · exact stieltjesTail_eq_of_active_prefix

end PowerSeries
