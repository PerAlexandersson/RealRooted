/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree lemmas for sums and products of polynomials

Degree and coefficient lemmas for sums, quotients by a linear factor, and products of polynomials.
They cover the degree of `p + C a * q` in several regimes (`q` of smaller degree, `q` of larger
degree, equal degree with a nonvanishing top coefficient), the degree of
`∑ k ∈ range (n + 1), C (a k) * X ^ (n - k)`, and the second-highest coefficient of a product.

## Main statements

* `Polynomial.natDegree_divByMonic_X_sub_C`: `(p /ₘ (X - C r)).natDegree = p.natDegree - 1`.
* `Polynomial.natDegree_add_C_mul_of_natDegree_lt`: if `f.natDegree < g.natDegree` and `a ≠ 0`,
  then `(f + C a * g).natDegree = g.natDegree`.
* `Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt`: in that situation the leading coefficient is
  `a * g.leadingCoeff`.
* `Polynomial.coeff_mul_add_add_one_eq_of_natDegree_le`: the coefficient of `p * q` in degree
  `a + b + 1` when `p.natDegree ≤ a + 1` and `q.natDegree ≤ b + 1`.
-/

@[expose] public section

open BigOperators

namespace Polynomial

/-- A degree-box sum with descending exponents has degree at most its box
bound. -/
theorem natDegree_sum_range_C_mul_X_pow_sub_le {R : Type*} [Semiring R]
    (a : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), C (a k) * X ^ (n - k)).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro k _
  exact (natDegree_C_mul_X_pow_le (a k) (n - k)).trans (Nat.sub_le _ _)

/-- Dividing by a monic linear factor lowers natural degree by one. -/
theorem natDegree_divByMonic_X_sub_C {R : Type*} [Ring R] [Nontrivial R]
    (p : R[X]) (r : R) :
    (p /ₘ (X - C r)).natDegree = p.natDegree - 1 := by
  rw [natDegree_divByMonic p (monic_X_sub_C r), natDegree_X_sub_C]

/-- If `p` has strictly larger degree than `q`, then `p + C a * q` has the
same degree as `p`. -/
theorem natDegree_add_C_mul_eq_left_of_natDegree_lt
    {R : Type*} [Semiring R] {p q : R[X]} {a : R}
    (hdeg : q.natDegree < p.natDegree) :
    (p + C a * q).natDegree = p.natDegree :=
  natDegree_add_eq_left_of_natDegree_lt ((natDegree_C_mul_le a q).trans_lt hdeg)

/-- If `g` has strictly larger degree than `f`, then `f + C a * g` has the
same degree as `g`, provided `a ≠ 0`. -/
theorem natDegree_add_C_mul_of_natDegree_lt {R : Type*} [Semiring R] [NoZeroDivisors R]
    {f g : R[X]} {a : R} (ha : a ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (f + C a * g).natDegree = g.natDegree := by
  rw [natDegree_add_eq_right_of_natDegree_lt
    (by simpa [natDegree_C_mul (p := g) ha] using hdeg), natDegree_C_mul (p := g) ha]

/-- If `g` has strictly larger degree than `f`, then the leading coefficient of
`f + C a * g` is the scaled leading coefficient of `g`. -/
theorem leadingCoeff_add_C_mul_of_natDegree_lt {R : Type*} [Semiring R] [NoZeroDivisors R]
    {f g : R[X]} {a : R} (ha : a ≠ 0) (hdeg : f.natDegree < g.natDegree) :
    (f + C a * g).leadingCoeff = a * g.leadingCoeff := by
  rw [leadingCoeff, natDegree_add_C_mul_of_natDegree_lt ha hdeg, coeff_add, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt hdeg, zero_add]
  rfl

/-- If `q` has degree at most that of `p`, and the coefficient of degree
`p.natDegree` in `p + C a * q` does not vanish, then the sum keeps the degree
of `p`. -/
theorem natDegree_add_C_mul_eq_left_of_natDegree_le_of_coeff_add_ne_zero
    {R : Type*} [Semiring R] {p q : R[X]} {a : R}
    (hdeg : q.natDegree ≤ p.natDegree)
    (hcoeff : p.leadingCoeff + a * q.coeff p.natDegree ≠ 0) :
    (p + C a * q).natDegree = p.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_add_le _ _).trans <|
      max_le le_rfl ((natDegree_C_mul_le a q).trans hdeg)
  · rw [coeff_add, coeff_C_mul]
    change p.leadingCoeff + a * q.coeff p.natDegree ≠ 0
    exact hcoeff

/-- The coefficient of `p * q` one below the sum of degree bounds `a + 1`, `b + 1`: only the
two top pairs contribute. -/
theorem coeff_mul_add_add_one_eq_of_natDegree_le {R : Type*} [Semiring R] {p q : R[X]}
    {a b : ℕ} (hp : p.natDegree ≤ a + 1) (hq : q.natDegree ≤ b + 1) :
    (p * q).coeff (a + b + 1) = p.coeff (a + 1) * q.coeff b + p.coeff a * q.coeff (b + 1) := by
  rw [coeff_mul, Finset.sum_eq_add (a + 1, b) (a, b + 1)]
  · simp
  · rintro ⟨i, j⟩ hx hne
    rw [Finset.mem_antidiagonal] at hx
    simp only at hx
    by_cases hi : a + 1 < i
    · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hi)]
    · by_cases hj : b + 1 < j
      · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hj)]
      · exfalso
        obtain ⟨h1, h2⟩ := hne
        have : i = a + 1 ∨ i = a := by lia
        rcases this with rfl | rfl <;> simp_all <;> lia
  · intro h; exact absurd (by simp; lia) h
  · intro h; exact absurd (by simp; lia) h

end Polynomial
