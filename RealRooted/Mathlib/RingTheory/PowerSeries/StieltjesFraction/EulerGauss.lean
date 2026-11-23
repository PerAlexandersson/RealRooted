/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail

/-!
# The formal Euler–Gauss recurrence

A normalized family satisfying `G (k+1) - G k = a k * X * G (k+2)` gives
the Stieltjes fraction with numerator data `a`. Quotients of adjacent
constant-term-one series satisfy the unique Stieltjes tail equations.
This is purely formal and requires neither nonzero numerators nor order.

See Sokal, "A simple algorithm for expanding a power series as a continued
fraction", Section 2 and Proposition 9.2. Here `G 0` is the source's `g₋₁`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A right inverse of a Stieltjes denominator equals its formal Stieltjes step. -/
theorem eq_stieltjesStep_of_mul_eq_one {a : R} {f g : R⟦X⟧}
    (h : (1 - C a * X * f) * g = 1) : g = stieltjesStep a f := by
  calc
    g = g * ((1 - C a * X * f) * stieltjesStep a f) := by
      rw [one_sub_mul_stieltjesStep, mul_one]
    _ = ((1 - C a * X * f) * g) * stieltjesStep a f := by ring
    _ = stieltjesStep a f := by rw [h, one_mul]

/-- The Euler–Gauss recurrence with `G 0 = 1` represents `G 1` by the
formal Stieltjes fraction. Every later constant term is forced to be one. -/
theorem eq_stieltjesTail_of_eulerGauss {a : ℕ → R} {G : ℕ → R⟦X⟧}
    (h0 : G 0 = 1)
    (hrec : ∀ k, G (k + 1) - G k = C (a k) * X * G (k + 2)) :
    G 1 = stieltjesTail a 0 := by
  have hconst (k : ℕ) : constantCoeff (G k) = 1 := by
    induction k with
    | zero => simp only [h0, map_one]
    | succ k ih =>
        have h := congrArg constantCoeff (hrec k)
        simp only [map_sub, map_mul, constantCoeff_X, mul_zero, zero_mul] at h
        exact (sub_eq_zero.mp h).trans ih
  let I : ℕ → R⟦X⟧ := fun k => invOfUnit (G k) 1
  have hi (k : ℕ) : G k * I k = 1 :=
    mul_invOfUnit (G k) 1 (by simpa using hconst k)
  have hi' (k : ℕ) : I k * G k = 1 := by rw [mul_comm]; exact hi k
  let F : ℕ → R⟦X⟧ := fun k => G (k + 1) * I k
  have hf (k : ℕ) : F k = stieltjesStep (a k) (F (k + 1)) := by
    apply eq_stieltjesStep_of_mul_eq_one
    have heq : G (k + 1) - C (a k) * X * G (k + 2) = G k := by
      linear_combination hrec k
    change (1 - C (a k) * X * (G (k + 1 + 1) * I (k + 1))) *
      (G (k + 1) * I k) = 1
    calc
      _ = G (k + 1) * I k - C (a k) * X * G (k + 2) *
          (I (k + 1) * G (k + 1)) * I k := by ring
      _ = (G (k + 1) - C (a k) * X * G (k + 2)) * I k := by
        rw [hi' (k + 1)]
        ring
      _ = 1 := by rw [heq, hi]
  have hF : F = stieltjesTail a := eq_stieltjesTail_of_step_eq hf
  have hi0 : I 0 = 1 := by simpa only [h0, one_mul] using hi 0
  simpa only [F, Nat.zero_add, hi0, mul_one] using congrFun hF 0

end PowerSeries
