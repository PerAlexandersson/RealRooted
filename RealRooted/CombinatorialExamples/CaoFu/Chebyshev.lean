/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The binomial polynomial in the Cao--Fu trace calculation

We prove the recurrence and the Chebyshev evaluation of the polynomial
`p_n(z) = ∑ (-1)^i choose(n+i,2i) z^i` used in Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2. Its identification with the determinant of
the minimum-entry matrix is a separate matrix-algebra statement.
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.CaoFu

/-- The binomial polynomial associated with the minimum-entry transfer matrix. -/
def traceDenominator (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range (n + 1), C ((-1 : ℝ) ^ i * (Nat.choose (n + i) (2 * i) : ℝ)) * X ^ i

/-- Every coefficient is given by the binomial formula, including beyond the degree. -/
theorem traceDenominator_coeff (n i : ℕ) :
    (traceDenominator n).coeff i = (-1 : ℝ) ^ i * (Nat.choose (n + i) (2 * i) : ℝ) := by
  classical
  unfold traceDenominator
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hi : i ≤ n
  · simp [hi]
  · have hni : n + i < 2 * i := by lia
    simp [hi, Nat.choose_eq_zero_of_lt hni]

/-- The binomial polynomial has constant coefficient one. -/
@[simp] theorem traceDenominator_coeff_zero (n : ℕ) :
    (traceDenominator n).coeff 0 = 1 := by rw [traceDenominator_coeff]; simp

/-- The binomial polynomial has degree exactly its matrix-size parameter. -/
theorem traceDenominator_natDegree (n : ℕ) : (traceDenominator n).natDegree = n := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [traceDenominator_coeff, Nat.choose_eq_zero_of_lt (by lia)]
    simp
  · apply le_natDegree_of_ne_zero
    rw [traceDenominator_coeff, show n + n = 2 * n by lia, Nat.choose_self, Nat.cast_one,
      mul_one]
    exact pow_ne_zero _ (by norm_num)

private theorem choose_second_difference (a k : ℕ) :
    Nat.choose (a + 2) (k + 2) + Nat.choose a (k + 2) =
      2 * Nat.choose (a + 1) (k + 2) + Nat.choose a k := by
  rw [show a + 2 = (a + 1) + 1 by lia, show k + 2 = (k + 1) + 1 by lia,
    Nat.choose_succ_succ', Nat.choose_succ_succ', Nat.choose_succ_succ']
  lia

/-- The two initial binomial polynomials. -/
@[simp] theorem traceDenominator_zero : traceDenominator 0 = 1 := by
  simp [traceDenominator]

/-- The size-one binomial polynomial. -/
@[simp] theorem traceDenominator_one : traceDenominator 1 = 1 - X := by
  norm_num [traceDenominator, sum_range_succ]
  ring

/-- The binomial polynomial satisfies the Chebyshev recurrence. -/
theorem traceDenominator_add_two (n : ℕ) :
    traceDenominator (n + 2) = (C 2 - X) * traceDenominator (n + 1) -
      traceDenominator n := by
  ext i
  cases i with
  | zero => norm_num
  | succ i =>
    rw [sub_mul, coeff_sub, coeff_sub, coeff_C_mul, coeff_X_mul]
    simp only [traceDenominator_coeff]
    have h := choose_second_difference (n + i + 1) (2 * i)
    have hidx : 2 * (i + 1) = 2 * i + 2 := by lia
    have hreal : (Nat.choose (n + (i + 1) + 2) (2 * (i + 1)) : ℝ) +
        (Nat.choose (n + (i + 1)) (2 * (i + 1)) : ℝ) =
        2 * (Nat.choose (n + (i + 1) + 1) (2 * (i + 1)) : ℝ) +
        (Nat.choose (n + (i + 1)) (2 * i) : ℝ) := by
      exact_mod_cast (by simpa only [hidx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
    have hchoose : Nat.choose (n + (i + 1)) (2 * i) = Nat.choose (n + 1 + i) (2 * i) := by
      congr 1; lia
    rw [hchoose] at hreal
    have ha : n + 2 + (i + 1) = n + (i + 1) + 2 := by lia
    have hb : n + 1 + (i + 1) = n + (i + 1) + 1 := by lia
    rw [ha, hb, pow_succ]
    linear_combination -((-1 : ℝ) ^ i) * hreal

/-- The binomial polynomial evaluates to the odd-angle cosine quotient. -/
theorem traceDenominator_eval_sin_sq_mul_cos (n : ℕ) (x : ℝ) :
    (traceDenominator n).eval (4 * Real.sin x ^ 2) * Real.cos x =
      Real.cos ((2 * (n : ℝ) + 1) * x) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [traceDenominator_one]
    simp only [eval_sub, eval_one, eval_X, Nat.cast_one]
    norm_num
    rw [Real.cos_three_mul]
    linear_combination -4 * Real.cos x * (Real.sin_sq_add_cos_sq x)
  | more n ih0 ih1 =>
    rw [traceDenominator_add_two, eval_sub, eval_mul, eval_sub, eval_C, eval_X, sub_mul,
      mul_assoc, ih1, ih0]
    have htrig := Real.two_mul_cos_mul_cos ((2 * (n + 1 : ℕ) + 1 : ℝ) * x) (2 * x)
    rw [Real.cos_two_mul_eq_one_sub] at htrig
    have hm : ((2 * (n + 1 : ℕ) + 1 : ℝ) * x) - 2 * x = (2 * (n : ℝ) + 1) * x := by
      push_cast; ring
    have hp : ((2 * (n + 1 : ℕ) + 1 : ℝ) * x) + 2 * x =
        (2 * (n + 2 : ℕ) + 1 : ℝ) * x := by push_cast; ring
    rw [hm, hp] at htrig
    nlinarith

end RealRooted.CaoFu
