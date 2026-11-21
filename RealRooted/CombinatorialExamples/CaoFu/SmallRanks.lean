module

public import RealRooted.CombinatorialExamples.CaoFu.Basic
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.CombinatorialExamples.CaoFu.Roots
import Mathlib.Tactic

/-!
# The small-rank Cao–Fu polynomials

We verify the exceptional rank-two polynomial in Cao–Fu,
*Real-rooted Ehrhart h*-polynomials of crown posets and wheel and whirl matroids*,
arXiv:2610.40496v1, equation (3.9), and the rank-three comparison grid in
Section 4.1, immediately after Lemma 4.1. The rank-three result is uniform
in the real parameter `lam ∈ [0,1]`.
-/

public section

open Polynomial Finset

namespace RealRooted.CaoFu

private theorem trace_two_one : transferTrace 2 1 = 7 := by
  norm_num [transferTrace, Matrix.trace, Matrix.diag, pow_succ, Matrix.mul_apply,
    Fin.sum_univ_succ]

private theorem trace_three_one : transferTrace 3 1 = 18 := by
  norm_num [transferTrace, Matrix.trace, Matrix.diag, pow_succ, Matrix.mul_apply,
    Fin.sum_univ_succ]

private theorem trace_three_two : transferTrace 3 2 = 129 := by
  norm_num [transferTrace, Matrix.trace, Matrix.diag, pow_succ, Matrix.mul_apply,
    Fin.sum_univ_succ]

/-- The exceptional rank-two polynomial is `(1+t)^2`, Cao–Fu, equation (3.9). -/
theorem crownPolynomial_zero : crownPolynomial 0 = (1 + X) ^ 2 := by
  have hlow : lowerPolynomial 0 = 1 := by
    simp [lowerPolynomial]
  have hmid : numeratorCoeff 2 1 = 2 := by
    norm_num [numeratorCoeff, sum_range_succ, trace_two_one]
  rw [crownPolynomial, hlow, hmid, reflect_one]
  norm_num [C_ofNat]
  ring

/-- Rank two is real-rooted, with a double root at `-1`. -/
theorem crownPolynomial_zero_roots :
    (crownPolynomial 0).Splits ∧ (crownPolynomial 0).roots = {-1, -1} := by
  rw [crownPolynomial_zero]
  constructor
  · simpa [add_comm] using (Polynomial.Splits.X_add_C (1 : ℝ)).pow 2
  · have h : (1 + X : ℝ[X]) = X - C (-1 : ℝ) := by simp; ring
    rw [h, roots_pow, roots_X_sub_C]
    norm_num [Multiset.nsmul_singleton]

/-- The explicit quartic in Cao–Fu, Section 4.1. -/
theorem crownPolynomial_one :
    crownPolynomial 1 = X ^ 4 + C 11 * X ^ 3 + C 24 * X ^ 2 + C 11 * X + 1 := by
  have hcoeff : numeratorCoeff 3 1 = 11 := by
    norm_num [numeratorCoeff, sum_range_succ, trace_three_one]
  have hmid : numeratorCoeff 3 2 = 24 := by
    norm_num [numeratorCoeff, sum_range_succ, trace_three_one, trace_three_two, Nat.choose]
  have hlow : lowerPolynomial 1 = 1 + C 11 * X := by
    norm_num [lowerPolynomial, sum_range_succ, hcoeff]
  rw [crownPolynomial, hlow, hmid, reflect_add, reflect_one, reflect_C_mul]
  have hx : (X : ℝ[X]).reflect 4 = X ^ 3 := by
    simpa using reflect_monomial (R := ℝ) 4 1
  norm_num only [Nat.reduceAdd, Nat.reduceMul] at *
  rw [hx]
  ring

/-- The rank-three correction is `t+4t²+t³`. -/
theorem correction_one : correction 1 = X + C 4 * X ^ 2 + X ^ 3 := by
  norm_num [correction, binomialSquare, sum_range_succ, C_ofNat]
  ring

private noncomputable def rankThreeGrid : Fin 3 → ℝ := ![-1, -(1 / 3), 0]

private theorem rankThreeGrid_strictMono : StrictMono rankThreeGrid := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [rankThreeGrid] at *

/-- The rank-three segment has four distinct negative roots for every real
`lam ∈ [0,1]`, as proved explicitly after Cao–Fu, Lemma 4.1. -/
theorem pencil_one_roots {lam : ℝ} (hlam : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    (pencil 1 lam).natDegree = 4 ∧ (pencil 1 lam).Splits ∧
      (pencil 1 lam).roots.Nodup ∧ ∀ z ∈ (pencil 1 lam).roots, z < 0 := by
  apply pencil_roots_of_sign_domination (by norm_num) rankThreeGrid
    rankThreeGrid_strictMono (by norm_num [rankThreeGrid])
    (by change rankThreeGrid 2 = 0; norm_num [rankThreeGrid]) _ hlam hlam₁
  intro i
  fin_cases i <;> norm_num [rankThreeGrid, crownPolynomial_one, correction_one]

end RealRooted.CaoFu
