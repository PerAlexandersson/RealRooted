/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.Basic
public import RealRooted.IntervalDifferential.Basic
import RealRooted.IntervalDifferential.CenteredBasis
import Mathlib.Tactic

/-!
# Parity of the crown coefficient expansion

Reciprocity of the explicit crown numerator makes its coefficient expansion in
the centered zig-zag basis even. This is the parity input for the alternative
centered-disk proof of Cao--Fu, arXiv:2610.40496v1, Theorem 1.1.
The equality with the analytic centered Ehrhart quotient of Lemmas 3.1--3.2,
and its disk bound, are not asserted here.
-/

public section

open Polynomial Finset RealRooted.IntervalDifferential

noncomputable section

namespace RealRooted.CaoFu

/-- The centered basis expansion of the crown numerator is even in every rank. -/
theorem crownPolynomial_centered_comp_neg_X (n : ℕ) :
    (∑ i ∈ range (2 * (n + 1) + 1),
      C ((crownPolynomial n).coeff i) * zigzagBasis i (2 * (n + 1) - i)).comp (-X) =
        ∑ i ∈ range (2 * (n + 1) + 1),
          C ((crownPolynomial n).coeff i) * zigzagBasis i (2 * (n + 1) - i) := by
  have hcoeff (i : ℕ) (hi : i ≤ 2 * (n + 1)) :
      (crownPolynomial n).coeff (2 * (n + 1) - i) = (crownPolynomial n).coeff i := by
    have h := congrArg (fun p : ℝ[X] => p.coeff i) (crownPolynomial_reflect n)
    simpa only [coeff_reflect, revAt_le hi] using h
  simpa only [pow_mul, neg_one_sq, one_pow, one_mul] using
    zigzagBasis_coeff_sum_comp_neg_X (2 * (n + 1)) (crownPolynomial n) hcoeff

end RealRooted.CaoFu
