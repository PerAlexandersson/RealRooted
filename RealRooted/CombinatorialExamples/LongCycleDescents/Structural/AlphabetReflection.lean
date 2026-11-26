/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.AlphabetRecurrence
import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.Factorization
public import RealRooted.IntervalDifferential.EulerRecurrence
import Mathlib.Tactic

/-!
# Alphabet coefficients indexed by degree loss

Reflection turns the genuine alphabet recurrence into the coefficient recurrence
used for the disk estimate. The parameter of reflection is the permutation size,
including when the alphabet polynomial vanishes.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace RealRooted.LongCycleDescents.Structural

private theorem reflect_sum {R ι : Type*} [Semiring R] (s : Finset ι)
    (f : ι → R[X]) (n : ℕ) :
    reflect n (∑ i ∈ s, f i) = ∑ i ∈ s, reflect n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [sum_insert ha, reflect_add, ih, sum_insert ha]

/-- Degree bound for a primitive-necklace polynomial. -/
theorem natDegree_necklacePolynomial_le (j : ℕ) :
    (necklacePolynomial j).natDegree ≤ j := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro d _
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans (Nat.div_le_self _ _))

/-- The alphabet recurrence kernel has degree at most its outer degree. -/
theorem natDegree_alphabetKernel_le (k i : ℕ) : (alphabetKernel k i).natDegree ≤ i := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  by_cases h : k ≤ j + 1 ∧ j + 1 ∣ i
  · simp only [ite_eq_left h]
    rw [← C_eq_natCast]
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_necklacePolynomial_le _).trans (by simpa using mem_range.mp hj))
  · simp [h]

/-- The faithful alphabet row is supported in degrees at most its size. -/
theorem natDegree_alphabetRow_le (n k : ℕ) : (alphabetRow k n).natDegree ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [← natDegree_map_eq_of_injective (Rat.castHom ℝ).injective,
      map_alphabetRow (Nat.pos_of_ne_zero hn)]
    exact natDegree_descentAlphabetPolynomial_le n k

/-- The alphabet polynomial reflected at the permutation size. -/
def lossRow (k n : ℕ) : ℚ[X] := reflect n (alphabetRow k n)

/-- Reflection at the permutation size keeps the degree at most that size. -/
theorem natDegree_lossRow_le (k n : ℕ) : (lossRow k n).natDegree ≤ n := by
  exact natDegree_reflect_le.trans (max_le le_rfl (natDegree_alphabetRow_le n k))

/-- The reflected divisor kernel, written without rational denominators. -/
def lossKernel (k i : ℕ) : ℚ[X] :=
  ∑ j ∈ range i, if k ≤ j + 1 ∧ j + 1 ∣ i then
    ∑ d ∈ (j + 1).divisors, C (μ d : ℚ) * X ^ (i - (j + 1) / d) else 0

/-- Reflection cancels the length denominator in each necklace polynomial. -/
theorem reflect_alphabetKernel (k i : ℕ) : reflect i (alphabetKernel k i) = lossKernel k i := by
  rw [alphabetKernel, reflect_sum, lossKernel]
  apply sum_congr rfl
  intro j hj
  by_cases h : k ≤ j + 1 ∧ j + 1 ∣ i
  · rw [ite_eq_left h, ite_eq_left h, ← C_eq_natCast, necklacePolynomial, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ (by positivity : ((j + 1 : ℕ) : ℚ) ≠ 0), C_1, one_mul, reflect_sum]
    apply sum_congr rfl
    intro d _
    rw [reflect_C_mul_X_pow, revAt_le]
    exact (Nat.div_le_self _ _).trans (by simpa using mem_range.mp hj)
  · simp [h]

@[simp] theorem lossRow_zero (k : ℕ) : lossRow k 0 = 1 := by simp [lossRow]

/-- The exact recurrence in degree-loss coordinates. -/
theorem lossRow_equation (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ[X]) * lossRow k n =
      ∑ i ∈ range n, lossKernel k (n - i) * lossRow k i := by
  have he := congrArg (reflect n) (alphabetRow_equation k hn)
  rw [← C_eq_natCast, reflect_C_mul, reflect_sum] at he
  rw [← C_eq_natCast]
  change C (n : ℚ) * lossRow k n = _ at he
  refine he.trans (sum_congr rfl ?_)
  intro i hi
  have hin := mem_range.mp hi
  conv_lhs => arg 1; rw [show n = (n - i) + i by lia]
  rw [reflect_mul _ _ (natDegree_alphabetKernel_le _ _)
    (natDegree_alphabetRow_le _ _), reflect_alphabetKernel]
  rfl

/-- The faithful alphabet recurrence is the canonical Euler coefficient row. -/
theorem lossRow_eq_eulerCoeff (k : ℕ) :
    lossRow k = PowerSeries.eulerCoeff (lossKernel k) := by
  apply PowerSeries.eulerCoeff_unique
  · exact lossRow_zero k
  · intro n hn
    simpa only [smul_eq_C_mul, C_eq_natCast] using lossRow_equation k hn

end RealRooted.LongCycleDescents.Structural
