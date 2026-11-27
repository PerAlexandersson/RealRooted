/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-!
# Catalan strict-peak polynomials by their coefficient formula

We define the family algebraically, without a word model. For positive `n`,
`C_n(t) = ∑ i, choose(n-i,i) choose(2n-3i,n-2i-1) (t-1)^i / (n-i)`.
The empty row is one. The degree bound is `floor((n-1)/2)`.

Source: ProgramComputer, *Strict peaks in Catalan words*, coefficient formula
and finite-certificate method, ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks

open Polynomial Finset

/-- The degree of the length-`n` row, including the constant initial rows. -/
def rowDegree (n : ℕ) : ℕ := (n - 1) / 2

/-- The coefficient of `(t - 1)^i`, evaluated in exact rational arithmetic. -/
def shiftedCoefficient (n i : ℕ) : ℚ :=
  (Nat.fast_choose (n - i) i : ℚ) * Nat.fast_choose (2 * n - 3 * i) (n - 2 * i - 1) /
    (n - i : ℕ)

/-- The strict-peak row defined by the explicit coefficient formula. -/
def polynomial (n : ℕ) : ℝ[X] :=
  if n = 0 then 1 else
    ∑ i ∈ range (rowDegree n + 1), C (shiftedCoefficient n i : ℝ) * (X - 1) ^ i

/-- Rational evaluation used by the exact sign checker. -/
def rationalValue (n : ℕ) (x : ℚ) : ℚ :=
  if n = 0 then 1 else
    ∑ i ∈ range (rowDegree n + 1), shiftedCoefficient n i * (x - 1) ^ i

/-- The executable coefficient is exactly the stated binomial expression. -/
theorem shiftedCoefficient_eq (n i : ℕ) :
    shiftedCoefficient n i =
      ((n - i).choose i : ℚ) * (2 * n - 3 * i).choose (n - 2 * i - 1) / (n - i : ℕ) := by
  simp only [shiftedCoefficient, ← Nat.choose_eq_fast_choose]

/-- Exact rational evaluation agrees with real evaluation of the defined polynomial. -/
theorem eval_polynomial_rat (n : ℕ) (x : ℚ) :
    (polynomial n).eval (x : ℝ) = (rationalValue n x : ℝ) := by
  simp only [polynomial, rationalValue]
  split
  · simp only [eval_one, Rat.cast_one]
  · simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one,
      Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_one]

/-- Every row has degree at most the size predicted by the formula. -/
theorem natDegree_polynomial_le (n : ℕ) : (polynomial n).natDegree ≤ rowDegree n := by
  unfold polynomial
  split
  · simp only [natDegree_one, zero_le]
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    refine (natDegree_mul_le.trans ?_).trans (Nat.le_of_lt_succ (mem_range.mp hi))
    simp only [natDegree_C, zero_add, natDegree_pow]
    have hlin : (X - 1 : ℝ[X]).natDegree = 1 := by
      simpa only [map_one] using natDegree_X_sub_C (1 : ℝ)
    simp only [hlin, Nat.mul_one, le_refl]

/-- Every shifted coefficient in the stated range is strictly positive. -/
theorem shiftedCoefficient_pos {n i : ℕ} (hn : n ≠ 0) (hi : i ≤ rowDegree n) :
    0 < shiftedCoefficient n i := by
  have hi' : 2 * i ≤ n - 1 := by unfold rowDegree at hi; lia
  rw [shiftedCoefficient_eq]
  exact div_pos (mul_pos (by exact_mod_cast Nat.choose_pos (show i ≤ n - i by lia))
    (by exact_mod_cast Nat.choose_pos (show n - 2 * i - 1 ≤ 2 * n - 3 * i by lia)))
    (by exact_mod_cast (show 0 < n - i by lia))

/-- The highest prospective coefficient of a positive-length row. -/
theorem coeff_polynomial_rowDegree {n : ℕ} (hn : n ≠ 0) :
    (polynomial n).coeff (rowDegree n) = (shiftedCoefficient n (rowDegree n) : ℝ) := by
  rw [polynomial, ite_eq_right hn, sum_range_succ, coeff_add, finsetSum_coeff]
  have hzero : ∑ i ∈ range (rowDegree n),
      (C (shiftedCoefficient n i : ℝ) * (X - 1) ^ i).coeff (rowDegree n) = 0 := by
    apply sum_eq_zero
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (natDegree_mul_le.trans ?_) (mem_range.mp hi)
    simp only [natDegree_C, zero_add, natDegree_pow]
    have hlin : (X - 1 : ℝ[X]).natDegree = 1 := by
      simpa only [map_one] using natDegree_X_sub_C (1 : ℝ)
    simp only [hlin, Nat.mul_one, le_refl]
  rw [hzero, zero_add, coeff_C_mul]
  have htop : ((X - 1 : ℝ[X]) ^ rowDegree n).coeff (rowDegree n) = 1 := by
    have hlin : (X - 1 : ℝ[X]).natDegree = 1 := by
      simpa only [map_one] using natDegree_X_sub_C (1 : ℝ)
    have hlead : (X - 1 : ℝ[X]).leadingCoeff = 1 := by
      simpa only [map_one] using (monic_X_sub_C (1 : ℝ)).leadingCoeff
    have h := coeff_pow_mul_natDegree (X - 1 : ℝ[X]) (rowDegree n)
    simpa only [hlin, Nat.mul_one, hlead, one_pow] using h
  rw [htop, mul_one]

/-- The formula attains its degree bound at every length. -/
theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = rowDegree n := by
  by_cases hn : n = 0
  · subst n
    simp only [polynomial, ite_true, natDegree_one, rowDegree, Nat.zero_sub, Nat.zero_div]
  · apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_polynomial_le n)
    rw [coeff_polynomial_rowDegree hn]
    exact ne_of_gt (by exact_mod_cast shiftedCoefficient_pos hn (le_refl (rowDegree n)))

/-- The leading coefficient is positive, including the constant initial rows. -/
theorem leadingCoeff_polynomial_pos (n : ℕ) : 0 < (polynomial n).leadingCoeff := by
  by_cases hn : n = 0
  · subst n
    simp only [polynomial, ite_true, leadingCoeff_one, zero_lt_one]
  · rw [leadingCoeff, natDegree_polynomial, coeff_polynomial_rowDegree hn]
    exact_mod_cast shiftedCoefficient_pos hn (le_refl (rowDegree n))

/-- Consecutive rows have equal degree bounds or differ by one. -/
theorem rowDegree_succ (n : ℕ) :
    rowDegree (n + 1) = rowDegree n ∨ rowDegree (n + 1) = rowDegree n + 1 := by
  unfold rowDegree
  lia

end RealRooted.CatalanWordPeaks
