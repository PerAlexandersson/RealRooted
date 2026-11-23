/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Complementary
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Coefficients
import Mathlib.Tactic.TypeStar

/-!
# Coefficient convolution for complementary Wall fractions
-/

public section

open scoped BigOperators

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The coefficient convolution of complementary formal chains is `L^n`.
This is the scaled coefficient form of the Kim-Zeng/Wall identity. -/
theorem sum_coeff_stieltjesTail_complementary {L : R} {u a b : ℕ → R}
    (ha0 : a 0 = L * u 0) (hb0 : b 0 = L * (1 - u 0))
    (ha : ∀ n, a (n + 1) = L * (1 - u n) * u (n + 1))
    (hb : ∀ n, b (n + 1) = L * u n * (1 - u (n + 1))) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      coeff ij.1 (stieltjesTail a 0) * coeff ij.2 (stieltjesTail b 0)) = L ^ n := by
  rw [← coeff_mul, stieltjesTail_mul_of_complementary_chain ha0 hb0 ha hb,
    coeff_stieltjesStep_one_eq_pow]

end PowerSeries
