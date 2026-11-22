/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.TypeStar

/-!
# Polynomial contraction and support

Contraction by a positive integer divides the degree bound by that integer.
It is inverse to expansion on polynomials supported at multiples of the stride.
-/

public section

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- Contraction by a nonzero stride divides the degree bound. -/
theorem natDegree_contract_le_div (p : R[X]) {r : ℕ} (hr : r ≠ 0) :
    (contract r p).natDegree ≤ p.natDegree / r := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_contract hr]
  exact coeff_eq_zero_of_natDegree_lt ((Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hr)).mp hn)

/-- Expansion undoes contraction when all nonzero coefficients occur at
indices divisible by the stride. -/
theorem expand_contract_of_coeff_eq_zero {p : R[X]} {r : ℕ} (hr : r ≠ 0)
    (hp : ∀ n, ¬r ∣ n → p.coeff n = 0) : expand R r (contract r p) = p := by
  ext n
  rw [coeff_expand (Nat.pos_of_ne_zero hr)]
  by_cases hn : r ∣ n
  · simp only [hn, ↓reduceIte, coeff_contract hr, Nat.div_mul_cancel hn]
  · simp [hn, hp n hn]

end Polynomial
