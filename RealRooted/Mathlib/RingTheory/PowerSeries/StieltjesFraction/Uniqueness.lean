/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Coefficients

/-!
# Uniqueness and termination of formal Stieltjes fractions

An active nonzero numerator can be recovered from the first coefficient and
cancelled to recover the next formal tail. Thus numerator coefficients are
unique until the first zero. Under the convention that every numerator after
the first zero also vanishes, the entire numerator sequence is unique.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A formal Stieltjes step with nonzero numerator determines its tail. -/
theorem stieltjesStep_injective [IsDomain R] {a : R} (ha : a ≠ 0) :
    Function.Injective (stieltjesStep a) := by
  intro f g h
  have hs : stieltjesStep a f ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    simp at hc
  have hc : (C a : R⟦X⟧) ≠ 0 := by
    intro hz
    have hconst := congrArg constantCoeff hz
    exact ha (by simpa using hconst)
  have hmul : (1 - C a * X * f) * stieltjesStep a f =
      (1 - C a * X * g) * stieltjesStep a f := by
    rw [one_sub_mul_stieltjesStep, h, one_sub_mul_stieltjesStep]
  have hd := mul_right_cancel₀ hs hmul
  apply mul_left_cancel₀ (mul_ne_zero hc X_ne_zero)
  linear_combination -hd

/-- Equal formal tails have equal first numerator coefficients. -/
theorem eq_of_stieltjesTail_eq {a b : ℕ → R} {s t : ℕ}
    (h : stieltjesTail a s = stieltjesTail b t) : a s = b t := by
  simpa only [coeff_one_stieltjesTail] using congrArg (coeff 1) h

/-- If the first numerator is nonzero, equal formal tails have equal next tails. -/
theorem stieltjesTail_succ_eq [IsDomain R] {a b : ℕ → R} {s t : ℕ}
    (h : stieltjesTail a s = stieltjesTail b t) (ha : a s ≠ 0) :
    stieltjesTail a (s + 1) = stieltjesTail b (t + 1) := by
  apply stieltjesStep_injective ha
  calc
    stieltjesStep (a s) (stieltjesTail a (s + 1)) = stieltjesTail a s :=
      (stieltjesTail_eq_step a s).symm
    _ = stieltjesTail b t := h
    _ = stieltjesStep (a s) (stieltjesTail b (t + 1)) := by
      rw [stieltjesTail_eq_step, eq_of_stieltjesTail_eq h]

/-- Equal formal fractions have equal numerator data up to the first zero.
No condition is imposed on later inactive numerator coefficients. -/
theorem eq_of_stieltjesTail_eq_of_prefix_ne_zero [IsDomain R] {a b : ℕ → R}
    {s t : ℕ} (n : ℕ) (h : stieltjesTail a s = stieltjesTail b t)
    (ha : ∀ i < n, a (s + i) ≠ 0) : a (s + n) = b (t + n) := by
  induction n generalizing s t with
  | zero => simpa only [Nat.add_zero] using eq_of_stieltjesTail_eq h
  | succ n ih =>
      have ha0 : a s ≠ 0 := by simpa only [Nat.add_zero] using ha 0 (by lia)
      have ht := stieltjesTail_succ_eq h ha0
      have hp : ∀ i < n, a (s + 1 + i) ≠ 0 := by
        intro i hi
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using ha (i + 1) (by lia)
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih ht hp

/-- With the usual zero-after-first-zero convention, all numerator coefficients
are uniquely determined by the normalized formal Stieltjes fraction. -/
theorem stieltjesTail_injective_of_zero_persists [IsDomain R] {a b : ℕ → R}
    (ha : ∀ i j, i ≤ j → a i = 0 → a j = 0)
    (hb : ∀ i j, i ≤ j → b i = 0 → b j = 0)
    (h : stieltjesTail a 0 = stieltjesTail b 0) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      by_cases hp : ∀ i < n, a i ≠ 0
      · simpa only [Nat.zero_add] using
          eq_of_stieltjesTail_eq_of_prefix_ne_zero n h (by simpa using hp)
      · push Not at hp
        obtain ⟨i, hin, hi⟩ := hp
        have hbi : b i = 0 := (ih i hin).symm.trans hi
        rw [ha i n (Nat.le_of_lt hin) hi, hb i n (Nat.le_of_lt hin) hbi]

/-- A negative active numerator cannot be represented by nonnegative numerator
data. Prior numerators must be nonzero, since a prior zero terminates the
fraction and makes the later negative value irrelevant. -/
theorem stieltjesTail_ne_of_active_neg {a b : ℕ → ℝ} {s t n : ℕ}
    (ha : ∀ i < n, a (s + i) ≠ 0) (hn : a (s + n) < 0)
    (hb : ∀ i, 0 ≤ b i) : stieltjesTail a s ≠ stieltjesTail b t := by
  intro h
  have heq := eq_of_stieltjesTail_eq_of_prefix_ne_zero n h ha
  exact (not_lt_of_ge (hb (t + n))) (heq ▸ hn)

end PowerSeries
