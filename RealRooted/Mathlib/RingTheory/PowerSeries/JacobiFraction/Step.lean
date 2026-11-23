/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal Jacobi continued-fraction steps

The inverse of `1 - b X - c X² f` is defined over an arbitrary commutative
ring. Its constant coefficient is one, and changes in the tail gain two
powers of `X`. In particular, a family of Jacobi tail equations has at most
one solution in formal power series.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- One Jacobi continued-fraction step. -/
@[expose] noncomputable def jacobiStep (b c : R) (f : R⟦X⟧) : R⟦X⟧ :=
  invOfUnit (1 - C b * X - C c * X ^ 2 * f) 1

/-- A formal Jacobi step has constant coefficient one. -/
@[simp] theorem constantCoeff_jacobiStep (b c : R) (f : R⟦X⟧) :
    constantCoeff (jacobiStep b c f) = 1 := by
  simp only [jacobiStep, constantCoeff_invOfUnit, inv_one, Units.val_one]

/-- A Jacobi step inverts its constant-term-one denominator. -/
theorem one_sub_mul_jacobiStep (b c : R) (f : R⟦X⟧) :
    (1 - C b * X - C c * X ^ 2 * f) * jacobiStep b c f = 1 := by
  exact mul_invOfUnit _ 1 (by simp)

/-- A right inverse of a Jacobi denominator equals its formal Jacobi step. -/
theorem eq_jacobiStep_of_mul_eq_one {b c : R} {f g : R⟦X⟧}
    (h : (1 - C b * X - C c * X ^ 2 * f) * g = 1) :
    g = jacobiStep b c f := by
  calc
    g = g * ((1 - C b * X - C c * X ^ 2 * f) * jacobiStep b c f) := by
      rw [one_sub_mul_jacobiStep, mul_one]
    _ = ((1 - C b * X - C c * X ^ 2 * f) * g) * jacobiStep b c f := by ring
    _ = jacobiStep b c f := by rw [h, one_mul]

/-- Difference identity for Jacobi steps with the same two coefficients. -/
theorem jacobiStep_sub (b c : R) (f g : R⟦X⟧) :
    jacobiStep b c f - jacobiStep b c g =
      C c * X ^ 2 * (f - g) * jacobiStep b c f * jacobiStep b c g := by
  linear_combination
    jacobiStep b c g * one_sub_mul_jacobiStep b c f -
      jacobiStep b c f * one_sub_mul_jacobiStep b c g

/-- A Jacobi step raises the order of a tail error by two. -/
theorem X_pow_dvd_jacobiStep_sub {n : ℕ} (b c : R) {f g : R⟦X⟧}
    (h : X ^ n ∣ f - g) : X ^ (n + 2) ∣ jacobiStep b c f - jacobiStep b c g := by
  obtain ⟨q, hq⟩ := h
  rw [jacobiStep_sub, hq]
  refine ⟨C c * q * jacobiStep b c f * jacobiStep b c g, ?_⟩
  rw [pow_add]
  ring

/-- Formal Jacobi tail equations have at most one solution, with no sign or
growth restrictions on either coefficient sequence. -/
theorem eq_of_jacobiStep_eq {b c : ℕ → R} {F G : ℕ → R⟦X⟧}
    (hF : ∀ s, F s = jacobiStep (b s) (c s) (F (s + 1)))
    (hG : ∀ s, G s = jacobiStep (b s) (c s) (G (s + 1))) : F = G := by
  have hdiv (n : ℕ) : ∀ s, X ^ (2 * n) ∣ F s - G s := by
    induction n with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        rw [hF s, hG s]
        simpa only [Nat.mul_succ] using
          X_pow_dvd_jacobiStep_sub (b s) (c s) (ih (s + 1))
  funext s
  ext k
  have h := X_pow_dvd_iff.mp (hdiv (k + 1) s) k (by lia)
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

end PowerSeries
