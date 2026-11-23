/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# A formal Stieltjes continued-fraction step

The denominator `1 - a X f` has constant coefficient one over any commutative
ring. Its inverse therefore exists in formal power series, without a fraction
field or an analytic convergence hypothesis. Changing the tail by a multiple
of `X^n` changes the step by a multiple of `X^(n+1)`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- One formal Stieltjes-fraction step, with a constant-term-one denominator. -/
@[expose] noncomputable def stieltjesStep (a : R) (f : R⟦X⟧) : R⟦X⟧ :=
  invOfUnit (1 - C a * X * f) 1

/-- A Stieltjes-fraction step has constant coefficient one. -/
@[simp] theorem constantCoeff_stieltjesStep (a : R) (f : R⟦X⟧) :
    constantCoeff (stieltjesStep a f) = 1 := by
  simp only [stieltjesStep, constantCoeff_invOfUnit, inv_one, Units.val_one]

/-- The formal Stieltjes step inverts its stated denominator. -/
theorem one_sub_mul_stieltjesStep (a : R) (f : R⟦X⟧) :
    (1 - C a * X * f) * stieltjesStep a f = 1 := by
  exact mul_invOfUnit _ 1 (by simp)

/-- A zero numerator discards the entire remaining formal tail. -/
@[simp] theorem stieltjesStep_zero (f : R⟦X⟧) : stieltjesStep (0 : R) f = 1 := by
  simpa using one_sub_mul_stieltjesStep (0 : R) f

/-- The additive recurrence underlying the Stieltjes--Rogers coefficients. -/
theorem stieltjesStep_eq_one_add (a : R) (f : R⟦X⟧) :
    stieltjesStep a f = 1 + C a * X * f * stieltjesStep a f := by
  linear_combination one_sub_mul_stieltjesStep a f

/-- Difference formula for two formal Stieltjes steps with the same numerator. -/
theorem stieltjesStep_sub (a : R) (f g : R⟦X⟧) :
    stieltjesStep a f - stieltjesStep a g =
      C a * X * (f - g) * stieltjesStep a f * stieltjesStep a g := by
  linear_combination
    stieltjesStep a g * one_sub_mul_stieltjesStep a f -
      stieltjesStep a f * one_sub_mul_stieltjesStep a g

/-- A formal Stieltjes step increases the order of a tail error by at least one. -/
theorem X_pow_dvd_stieltjesStep_sub {n : ℕ} (a : R) {f g : R⟦X⟧}
    (h : X ^ n ∣ f - g) : X ^ (n + 1) ∣ stieltjesStep a f - stieltjesStep a g := by
  obtain ⟨q, hq⟩ := h
  rw [stieltjesStep_sub, hq]
  refine ⟨C a * q * stieltjesStep a f * stieltjesStep a g, ?_⟩
  rw [pow_succ]
  ring

/-- A family satisfying the Stieltjes tail equations is unique. This is a
formal contraction argument, independent of signs, size bounds or convergence. -/
theorem eq_of_stieltjesStep_eq {a : ℕ → R} {F G : ℕ → R⟦X⟧}
    (hF : ∀ s, F s = stieltjesStep (a s) (F (s + 1)))
    (hG : ∀ s, G s = stieltjesStep (a s) (G (s + 1))) : F = G := by
  have hdiv (n : ℕ) : ∀ s, X ^ n ∣ F s - G s := by
    induction n with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        rw [hF s, hG s]
        exact X_pow_dvd_stieltjesStep_sub (a s) (ih (s + 1))
  funext s
  ext k
  have h := X_pow_dvd_iff.mp (hdiv (k + 1) s) k (Nat.lt_succ_self k)
  exact sub_eq_zero.mp (by simpa only [map_sub] using h)

end PowerSeries
