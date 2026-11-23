/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import Mathlib.Tactic.TypeStar

/-!
# The first discrepancy from a normalized linear exponential
-/

public section

namespace PowerSeries

variable {R : Type*} [Field R] [Algebra ℚ R]

/-- A nonexponential formal symbol with nonzero constant term first differs
from its matching scaled exponential at an order of at least two. -/
theorem exists_first_scaled_exponential_discrepancy {φ : PowerSeries R}
    (h0 : constantCoeff φ ≠ 0)
    (hne : φ ≠ C (constantCoeff φ) *
      rescale (coeff 1 φ / constantCoeff φ) (exp R)) :
    ∃ p : ℕ, 2 ≤ p ∧
      (∀ k < p, coeff k φ = constantCoeff φ *
        (coeff 1 φ / constantCoeff φ) ^ k / (k.factorial : R)) ∧
      coeff p φ ≠ constantCoeff φ *
        (coeff 1 φ / constantCoeff φ) ^ p / (p.factorial : R) := by
  classical
  have hex : ∃ p : ℕ, coeff p φ ≠ constantCoeff φ *
      (coeff 1 φ / constantCoeff φ) ^ p / (p.factorial : R) := by
    by_contra h
    apply hne
    ext k
    rw [coeff_C_mul, coeff_rescale_exp, ← mul_div_assoc]
    by_contra hk
    exact h ⟨k, hk⟩
  let p := Nat.find hex
  have hdiff : coeff p φ ≠ constantCoeff φ *
      (coeff 1 φ / constantCoeff φ) ^ p / (p.factorial : R) := Nat.find_spec hex
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hdiff
    exact hdiff (by simp only [coeff_zero_eq_constantCoeff, pow_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one, div_one])
  have hp1 : p ≠ 1 := by
    intro hp
    rw [hp] at hdiff
    exact hdiff (by simp only [pow_one, Nat.factorial_one, Nat.cast_one,
      div_one, mul_div_cancel₀ _ h0])
  refine ⟨p, by lia, ?_, hdiff⟩
  intro k hk
  exact not_ne_iff.mp (Nat.find_min hex hk)

/-- A normalized formal symbol which is not its matching linear exponential
has a first discrepancy of order at least two. -/
theorem exists_first_exponential_discrepancy {φ : PowerSeries R}
    (h0 : constantCoeff φ = 1)
    (hne : φ ≠ rescale (coeff 1 φ) (exp R)) :
    ∃ p : ℕ, 2 ≤ p ∧
      (∀ k < p, coeff k φ = coeff 1 φ ^ k / (k.factorial : R)) ∧
      coeff p φ ≠ coeff 1 φ ^ p / (p.factorial : R) := by
  simpa only [h0, map_one, one_mul, div_one] using
    exists_first_scaled_exponential_discrepancy
      (φ := φ) (by rw [h0]; exact one_ne_zero)
      (by simpa only [h0, map_one, one_mul, div_one] using hne)

end PowerSeries
