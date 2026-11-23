/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# Reflection of polynomials supported in even degrees
-/

public section

namespace Polynomial

/-- A polynomial whose odd coefficients vanish is unchanged by negating
its variable. This direction works over every commutative ring. -/
theorem comp_neg_X_eq_self_of_odd_coeff_eq_zero {R : Type*} [CommRing R]
    {p : R[X]} (h : ∀ k, Odd k → p.coeff k = 0) : p.comp (-X) = p := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  rw [sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_comp, C_comp, X_pow_comp]
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_pow]
  · rw [h k hk, map_zero, zero_mul, zero_mul]

/-- Removing all powers of `X` from a monic polynomial supported in even
degrees removes an even power and leaves the same support parity. -/
theorem Monic.exists_even_X_pow_mul {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p.Monic) (he : ∀ k, Odd k → p.coeff k = 0) :
    ∃ (m : ℕ) (q : R[X]), Even m ∧ q.Monic ∧ q.coeff 0 ≠ 0 ∧
      (∀ k, Odd k → q.coeff k = 0) ∧ p = X ^ m * q := by
  let m := p.natTrailingDegree
  have hmc : p.coeff m ≠ 0 := trailingCoeff_ne_zero.mpr hp.ne_zero
  have hm : Even m := by
    rcases Nat.even_or_odd m with h | h
    · exact h
    · exact (hmc (he m h)).elim
  have hdiv : X ^ m ∣ p := X_pow_dvd_iff.mpr fun k hk ↦
    coeff_eq_zero_of_lt_natTrailingDegree hk
  obtain ⟨q, hq⟩ := hdiv
  have hc (k : ℕ) : q.coeff k = p.coeff (k + m) := by
    rw [hq, coeff_X_pow_mul]
  refine ⟨m, q, hm, (monic_X_pow m).of_mul_monic_left (hq ▸ hp), ?_, ?_, hq⟩
  · simpa only [hc, zero_add] using hmc
  · intro k hk
    rw [hc, he (k + m) (hk.add_even hm)]

end Polynomial
