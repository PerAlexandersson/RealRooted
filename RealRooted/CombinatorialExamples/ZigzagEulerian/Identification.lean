/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions
public import RealRooted.IntervalDifferential.Basic

/-!
# The finite zig-zag operator identity

The polynomial here is the explicit finite factor sum from Appendix A.2 of
the zig-zag Eulerian proof. Its identification with the quotient
of the centered exponential generating function is a separate combinatorial
statement. This module proves the exact operator identity of Appendix A.3
and its rational-evaluation form for the actual permutation sum.
-/

@[expose] public section

open Polynomial Finset RealRooted.IntervalDifferential

noncomputable section

namespace RealRooted.ZigzagEulerian

/-- The finite factor sum in the centered variable, with one summand for each
actual up-down permutation. This is the candidate quotient in Appendix A.6. -/
def zigzagCenteredQuotient (n : ℕ) : ℝ[X] := by
  classical
  exact ∑ π ∈ (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown,
    zigzagBasis (swapCount π) (n - 2 - swapCount π)

/-- The finite homogenized sum of the actual swap enumerator. -/
def zigzagHomogenizedSum (n : ℕ) : ℝ[X] := by
  classical
  exact ∑ π ∈ (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown,
    (X - 1) ^ swapCount π * (X + 1) ^ (n - 2 - swapCount π)

private theorem zigzagTransform_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ[X]) :
    zigzagTransform (∑ i ∈ s, f i) = ∑ i ∈ s, zigzagTransform (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zigzagTransform, zigzagFunctionalCalculus]
  | @insert i s hi ih => simp [hi, zigzagTransform_add, ih]

/-- Appendix A.3, formula (A.7), summed over the actual alternating class.
The factor `2` is kept integral, so no division is needed. -/
theorem zigzagCenteredQuotient_transform (n : ℕ) (hn : 2 ≤ n) :
    C (2 : ℝ) * zigzagTransform (zigzagCenteredQuotient n) =
      C ((n.factorial : ℕ) : ℝ) * zigzagHomogenizedSum n := by
  classical
  rw [zigzagCenteredQuotient, zigzagHomogenizedSum, zigzagTransform_finsetSum]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  have hd := swapCount_le_sub_two hn π
  have hindex : swapCount π + (n - 2 - swapCount π) + 2 = n := by lia
  simpa only [hindex] using
    zigzagBasis_transform (swapCount π) (n - 2 - swapCount π)

private theorem zigzag_rational_monomial (D d : ℕ) (hd : d ≤ D)
    (z : ℝ) (hz : z + 1 ≠ 0) :
    (z + 1) ^ D * ((z - 1) / (z + 1)) ^ d =
      (z - 1) ^ d * (z + 1) ^ (D - d) := by
  have hsum : d + (D - d) = D := by lia
  have hsplit : (z + 1) ^ D = (z + 1) ^ d * (z + 1) ^ (D - d) := by
    rw [← pow_add, hsum]
  have hpow : (z + 1) ^ d ≠ 0 := pow_ne_zero d hz
  calc
    (z + 1) ^ D * ((z - 1) / (z + 1)) ^ d =
      ((z + 1) ^ d * (z + 1) ^ (D - d)) *
        ((z - 1) ^ d / (z + 1) ^ d) := by rw [hsplit, div_pow]
    _ = (z - 1) ^ d * (z + 1) ^ (D - d) := by field_simp

/-- Evaluation form of Appendix A.3, formula (I), for the actual permutation
polynomial and the finite centered quotient. -/
theorem zigzagCenteredQuotient_eval_identity (n : ℕ) (hn : 2 ≤ n)
    (z : ℝ) (hz : z + 1 ≠ 0) :
    (z + 1) ^ (n - 2) *
        (zigzagEulerianPolynomial n).eval ((z - 1) / (z + 1)) =
      (2 / (n.factorial : ℝ)) * (zigzagTransform (zigzagCenteredQuotient n)).eval z := by
  classical
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hpoly := zigzagCenteredQuotient_transform n hn
  have heval := congrArg (fun p : ℝ[X] => p.eval z) hpoly
  rw [zigzagHomogenizedSum] at heval
  simp only [eval_mul, eval_C, eval_finsetSum, eval_pow, eval_sub, eval_add,
    eval_X, eval_one] at heval
  have hsum : (z + 1) ^ (n - 2) *
      (zigzagEulerianPolynomial n).eval ((z - 1) / (z + 1)) =
        ∑ π ∈ (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown,
          (z - 1) ^ swapCount π * (z + 1) ^ (n - 2 - swapCount π) := by
    rw [zigzagEulerianPolynomial, eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [eval_pow, eval_X]
    exact zigzag_rational_monomial (n - 2) (swapCount π)
      (swapCount_le_sub_two hn π) z hz
  rw [hsum]
  apply (mul_left_cancel₀ hfac)
  calc
    (n.factorial : ℝ) *
        ∑ π ∈ (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown,
          (z - 1) ^ swapCount π * (z + 1) ^ (n - 2 - swapCount π) =
      2 * (zigzagTransform (zigzagCenteredQuotient n)).eval z := by
        simpa only [mul_comm] using heval.symm
    _ = (n.factorial : ℝ) *
        ((2 / (n.factorial : ℝ)) *
          (zigzagTransform (zigzagCenteredQuotient n)).eval z) := by
            field_simp

end RealRooted.ZigzagEulerian
