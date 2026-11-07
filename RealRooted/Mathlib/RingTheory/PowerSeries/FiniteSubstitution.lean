/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic

/-! # A bounded coefficient formula for formal substitution -/

public section

namespace PowerSeries

/-- A power of a series with zero constant term has no coefficients below
its exponent. -/
theorem coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R]
    (G : PowerSeries R) (hG : constantCoeff G = 0) {n j : ℕ} (h : n < j) :
    coeff n (G ^ j) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h)
    (le_order_pow_of_constantCoeff_eq_zero j hG)

/-- Only exponents at most the desired coefficient contribute to a formal
substitution with zero constant term. -/
theorem coeff_subst_eq_sum_range {R : Type*} [CommRing R]
    (G F : PowerSeries R) (hG : constantCoeff G = 0) (n : ℕ) :
    coeff n (subst G F) =
      ∑ j ∈ Finset.range (n + 1), coeff j F * coeff n (G ^ j) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hG)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra h
  have hnj : n < j := by lia
  change coeff j F * coeff n (G ^ j) ≠ 0 at hj
  exact hj (by rw [coeff_pow_eq_zero_of_lt G hG hnj, mul_zero])

end PowerSeries
