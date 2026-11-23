/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.EulerGauss

/-!
# Terminating Euler–Gauss recurrences
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A finite Euler–Gauss chain whose last two series agree yields the Stieltjes
fraction with every numerator after that position set to zero. This includes
the immediate termination `N = 0`. -/
theorem eq_stieltjesTail_of_eulerGauss_terminated
    {a : ℕ → R} {G : ℕ → R⟦X⟧} (N : ℕ) (h0 : G 0 = 1)
    (hrec : ∀ k < N, G (k + 1) - G k = C (a k) * X * G (k + 2))
    (hterm : G (N + 1) = G N) :
    G 1 = stieltjesTail (fun k => if k < N then a k else 0) 0 := by
  let H : ℕ → R⟦X⟧ := fun k => G (min k (N + 1))
  have hH (k : ℕ) : H (k + 1) - H k =
      C (if k < N then a k else 0) * X * H (k + 2) := by
    by_cases hk : k < N
    · simpa only [H, min_eq_left (by lia : k + 1 ≤ N + 1),
        min_eq_left (by lia : k ≤ N + 1), min_eq_left (by lia : k + 2 ≤ N + 1),
        ite_eq_left hk] using hrec k hk
    · rw [ite_eq_right hk, map_zero, zero_mul, zero_mul]
      by_cases heq : k = N
      · subst k
        simp only [H, min_self, min_eq_left (by lia : N ≤ N + 1), hterm, sub_self]
      · have hlarge : N + 1 ≤ k := by lia
        simp only [H, min_eq_right (by lia : N + 1 ≤ k + 1),
          min_eq_right hlarge, sub_self]
  have hH0 : H 0 = 1 := by simpa [H] using h0
  have hH1 : H 1 = G 1 := by simp only [H, min_eq_left (by lia : 1 ≤ N + 1)]
  simpa only [hH1] using eq_stieltjesTail_of_eulerGauss hH0 hH

end PowerSeries
