/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.FormalPrincipal
import RealRooted.Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# The normalized polynomial in the Cao--Fu trace representation

We define `S_r` from the principal-part coefficients in Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2, equation (3.2), and prove `S_r(1) = 1`
by formal coefficient extraction. Our parameter `n` denotes `r - 1`.
-/

@[expose] public section
noncomputable section
open PowerSeries Finset
open RealRooted.CenteredEulerian

namespace RealRooted.CaoFu

/-- The coefficient of `X^(2j+2)` in `X tan X`. -/
def tangentWeight (j : ℕ) : ℝ := eulerCoeff (2 * j + 1)

/-- The tangent weights are strictly positive. -/
theorem tangentWeight_pos (j : ℕ) : 0 < tangentWeight j := eulerCoeff_pos _

/-- The odd Euler coefficients are the coefficients of `X tan X`. -/
theorem coeff_X_mul_sinS_mul_secS (j : ℕ) :
    coeff (2 * (j + 1)) (X * sinS * secS) = tangentWeight j := by
  rw [mul_assoc, show 2 * (j + 1) = (2 * j + 1) + 1 by lia, coeff_succ_X_mul,
    tangentWeight, eulerCoeff_eq_beta, beta, beta, pow_zero, mul_one, pow_one]
  rw [isEvenPS_secS.coeff_odd (by exact ⟨j, rfl⟩), zero_add, mul_comm sinS]

private theorem coeff_odd_X_mul_sinS_mul_secS (j : ℕ) :
    coeff (2 * j + 1) (X * sinS * secS) = 0 := by
  rw [mul_assoc, coeff_succ_X_mul]
  simpa only [mul_comm] using
    (isEvenPS_secS.mul_odd isOddPS_sinS).coeff_even (even_two_mul j)

private theorem coeff_even_mul_inverseSineQuotient_pow (n : ℕ) (B : ℝ⟦X⟧)
    (hzero : coeff 0 B = 0) (hodd : ∀ j, coeff (2 * j + 1) B = 0) :
    coeff (2 * (n + 1)) (B * inverseSineQuotient ^ (2 * (n + 1))) =
      ∑ j ∈ range (n + 1), principalCoeff n j * coeff (2 * (j + 1)) B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_two_mul]
  simp only [hodd, zero_mul, add_zero]
  rw [← sum_range_succ, sum_range_succ']
  simp only [hzero, zero_mul, add_zero]
  apply sum_congr rfl
  intro j hj
  rw [show 2 * (n + 1) - 2 * (j + 1) = 2 * (n - j) by lia,
    ← principalCoeff_eq_coeff_inverseSineQuotient_pow n j
      (by have := mem_range.mp hj; lia)]
  ring

private theorem coeff_X_tangent_mul_pow (n : ℕ) :
    coeff (2 * (n + 1))
      ((X * sinS * secS) * inverseSineQuotient ^ (2 * (n + 1))) =
      ∑ j ∈ range (n + 1), principalCoeff n j * tangentWeight j := by
  rw [coeff_even_mul_inverseSineQuotient_pow n _
    (by rw [mul_assoc]; simp) coeff_odd_X_mul_sinS_mul_secS]
  simp only [coeff_X_mul_sinS_mul_secS]

/-- The principal-part and tangent coefficients have total weight one. -/
theorem sum_principalCoeff_mul_tangentWeight (n : ℕ) :
    (∑ j ∈ range (n + 1), principalCoeff n j * tangentWeight j) = 1 := by
  rw [← coeff_X_tangent_mul_pow]
  convert coeff_inverseSineQuotient_pow_mul_X_tangent n using 1
  congr 1
  ring

/-- The polynomial `S_(n+1)` in the trace representation. -/
def cosecantPolynomial (n : ℕ) : Polynomial ℝ :=
  ∑ j ∈ range (n + 1),
    Polynomial.C (principalCoeff n j * tangentWeight j) * Polynomial.X ^ (2 * (j + 1))

/-- The tangent weight is the positive odd-pole sum. -/
theorem tangentWeight_eq_odd_poles (j : ℕ) :
    tangentWeight j =
      2 * ∑' k : ℕ, (2 / ((2 * (k : ℝ) + 1) * Real.pi)) ^ (2 * (j + 1)) := by
  have hp : 2 * j + 1 + 1 = 2 * (j + 1) := by lia
  have ht : Tsum (2 * (j + 1)) = Ssum (2 * (j + 1)) := by
    apply tsum_congr
    intro k
    rw [tSeq, sSeq, div_pow, ← pow_mul, mul_comm (k + 1), pow_mul,
      (even_two_mul (j + 1)).neg_one_pow, one_pow, one_div_pow]
  have hs : Summable (fun k : ℕ => (1 / (2 * (k : ℝ) + 1)) ^ (2 * (j + 1))) := by
    apply (summable_nat_add_iff 1).mp
    refine (summable_sSeq (s := 2 * (j + 1)) (by lia)).congr fun k => ?_
    dsimp [sSeq]
    push_cast
    congr 2
    ring
  have hsum : (∑' k : ℕ, (1 / (2 * (k : ℝ) + 1)) ^ (2 * (j + 1))) =
      1 + Ssum (2 * (j + 1)) := by
    rw [hs.tsum_eq_zero_add]
    congr 1
    · norm_num
    · apply tsum_congr
      intro k
      simp only [sSeq, Nat.cast_add, Nat.cast_one]
      congr 2
      ring
  rw [tangentWeight, eulerCoeff_formula (by lia), hp, ht]
  calc
    _ = 2 * ((2 / Real.pi) ^ (2 * (j + 1)) *
        ∑' k : ℕ, (1 / (2 * (k : ℝ) + 1)) ^ (2 * (j + 1))) := by rw [hsum]; ring
    _ = _ := by
      rw [← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro k
      rw [← mul_pow]
      congr 1
      field_simp

/-- The coefficient normalization is the evaluation `S_r(1) = 1`. -/
@[simp] theorem cosecantPolynomial_eval_one (n : ℕ) :
    (cosecantPolynomial n).eval 1 = 1 := by
  simpa [cosecantPolynomial, Polynomial.eval_finsetSum] using sum_principalCoeff_mul_tangentWeight n

/-- The polynomial `S_r` vanishes at zero. -/
@[simp] theorem cosecantPolynomial_eval_zero (n : ℕ) :
    (cosecantPolynomial n).eval 0 = 0 := by
  simp [cosecantPolynomial, Polynomial.eval_finsetSum]

/-- Every exponent of the cosecant polynomial is even. -/
theorem cosecantPolynomial_comp_neg_X (n : ℕ) :
    (cosecantPolynomial n).comp (-Polynomial.X) = cosecantPolynomial n := by
  simp [cosecantPolynomial, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.C_comp, Polynomial.X_comp, Even.neg_pow (even_two_mul _)]

/-- The cosecant polynomial has value one at minus one. -/
@[simp] theorem cosecantPolynomial_eval_neg_one (n : ℕ) :
    (cosecantPolynomial n).eval (-1) = 1 := by
  simpa [cosecantPolynomial, Polynomial.eval_finsetSum, Even.neg_one_pow (even_two_mul _)] using
    sum_principalCoeff_mul_tangentWeight n

/-- The top coefficient of `S_(n+1)` is its positive tangent weight. -/
theorem cosecantPolynomial_coeff_top (n : ℕ) :
    (cosecantPolynomial n).coeff (2 * (n + 1)) = tangentWeight n := by
  classical
  rw [cosecantPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single n]
  · simp
  · intro j _ hj
    rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right (by intro h; apply hj; lia)]
  · simp

/-- The cosecant polynomial has the full degree `2r`. -/
theorem cosecantPolynomial_natDegree (n : ℕ) :
    (cosecantPolynomial n).natDegree = 2 * (n + 1) := by
  apply le_antisymm
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_X_pow_le _).trans
    have := mem_range.mp hj
    lia
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [cosecantPolynomial_coeff_top]
    exact (tangentWeight_pos n).ne'

/-- The centered trace polynomial `E_(n+1) = (S_(n+1)-1)/(2*4^(n+1))`. -/
def centeredTracePolynomial (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (2 * (4 : ℝ) ^ (n + 1))) * (cosecantPolynomial n - 1)

/-- The centered trace polynomial has full even degree. -/
theorem centeredTracePolynomial_natDegree (n : ℕ) :
    (centeredTracePolynomial n).natDegree = 2 * (n + 1) := by
  rw [centeredTracePolynomial, Polynomial.natDegree_C_mul (by positivity),
    show (1 : Polynomial ℝ) = Polynomial.C 1 by rfl, Polynomial.natDegree_sub_C,
    cosecantPolynomial_natDegree]

/-- The centered trace polynomial is even. -/
theorem centeredTracePolynomial_comp_neg_X (n : ℕ) :
    (centeredTracePolynomial n).comp (-Polynomial.X) = centeredTracePolynomial n := by
  simp [centeredTracePolynomial, Polynomial.mul_comp, Polynomial.sub_comp,
    cosecantPolynomial_comp_neg_X]

/-- The centered trace polynomial vanishes at one. -/
@[simp] theorem centeredTracePolynomial_eval_one (n : ℕ) :
    (centeredTracePolynomial n).eval 1 = 0 := by
  simp [centeredTracePolynomial]

/-- The centered trace polynomial vanishes at minus one. -/
@[simp] theorem centeredTracePolynomial_eval_neg_one (n : ℕ) :
    (centeredTracePolynomial n).eval (-1) = 0 := by
  simp [centeredTracePolynomial]

/-- The generating-function identity after the change of variable `s = sin X`.
This is the coefficient form of Cao--Fu equation (3.2), for arbitrary real `m`. -/
theorem cosecantPolynomial_eval_eq_coeff_tangent_subst_arcsin (n : ℕ) (m : ℝ) :
    (cosecantPolynomial n).eval m = coeff (2 * (n + 1))
      ((C m * (sinS * secS) * rescale m (sinS * secS)).subst fS) := by
  let B : ℝ⟦X⟧ := C m * X * rescale m (sinS * secS)
  have hzero : coeff 0 B = 0 := by simp [B, mul_assoc]
  have hodd (j : ℕ) : coeff (2 * j + 1) B = 0 := by
    dsimp [B]
    rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul, coeff_rescale]
    have h := (isEvenPS_secS.mul_odd isOddPS_sinS).coeff_even (even_two_mul j)
    rw [mul_comm secS] at h
    rw [h]
    ring
  have heven (j : ℕ) : coeff (2 * (j + 1)) B = tangentWeight j * m ^ (2 * (j + 1)) := by
    have ht := coeff_X_mul_sinS_mul_secS j
    rw [mul_assoc, show 2 * (j + 1) = (2 * j + 1) + 1 by lia, coeff_succ_X_mul] at ht
    dsimp [B]
    rw [mul_assoc, coeff_C_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by lia,
      coeff_succ_X_mul, coeff_rescale, ht]
    ring
  rw [coeff_subst_arcsin_eq_coeff_mul_cosS]
  have hprod : C m * (sinS * secS) * rescale m (sinS * secS) * cosS *
      inverseSineQuotient ^ (2 * (n + 1) + 1) =
      B * inverseSineQuotient ^ (2 * (n + 1)) := by
    calc
      _ = C m * rescale m (sinS * secS) * (sinS * inverseSineQuotient) *
          (cosS * secS) * inverseSineQuotient ^ (2 * (n + 1)) := by rw [pow_succ]; ring
      _ = _ := by rw [sinS_mul_inverseSineQuotient, cosS_mul_secS]; dsimp [B]; ring
  rw [hprod, coeff_even_mul_inverseSineQuotient_pow n B hzero hodd]
  simp only [heven, cosecantPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply sum_congr rfl
  intro j _
  ring

end RealRooted.CaoFu
