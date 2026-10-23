/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.RootSums
public import RealRooted.IntervalDifferential.LinearInsertion
public import Mathlib.Tactic

/-!
# Root signs for conjugate-pair insertion

Appendix C.2 of `alternating_eulerian_shorter_proof.md`: the disk bound,
the split-root inequalities, and the polynomial certificate imply the strict
opposite sign at every interior zero of the linear insertion that is not an
old root. No root-sum inequality is assumed by the caller.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- A quadratic spectral factor raises the degree twice. -/
theorem zigzagQuadraticFactor_natDegree (a b : ℝ) (F : ℝ[X]) (hF : F ≠ 0) :
    (zigzagQuadraticFactor a b F).natDegree = F.natDegree + 2 := by
  have hG := zigzagLinearFactor_ne_zero a F hF
  have hdeg := zigzagLinearFactor_natDegree a (zigzagLinearFactor a F) hG
  rw [zigzagLinearFactor_natDegree a F hF] at hdeg
  have hlow : (C (b ^ 2) * F).natDegree <
      (zigzagLinearFactor a (zigzagLinearFactor a F)).natDegree := by
    rw [hdeg]
    have h := natDegree_C_mul_le (b ^ 2) F
    lia
  rw [zigzagQuadraticFactor, natDegree_add_eq_left_of_natDegree_lt hlow, hdeg]

/-- Right endpoint evaluation for conjugate-pair insertion. -/
theorem zigzagQuadraticFactor_eval_one (a b : ℝ) (F : ℝ[X]) :
    (zigzagQuadraticFactor a b F).eval 1 = ((3 - a) ^ 2 + b ^ 2) * F.eval 1 := by
  simp only [zigzagQuadraticFactor, eval_add, eval_mul, eval_C,
    zigzagLinearFactor_eval_one]
  ring

/-- Left endpoint evaluation for conjugate-pair insertion. -/
theorem zigzagQuadraticFactor_eval_neg_one (a b : ℝ) (F : ℝ[X]) :
    (zigzagQuadraticFactor a b F).eval (-1) = ((3 + a) ^ 2 + b ^ 2) * F.eval (-1) := by
  simp only [zigzagQuadraticFactor, eval_add, eval_mul, eval_C,
    zigzagLinearFactor_eval_neg_one]
  ring

/-- The derivative sign at a linear-insertion root follows from the same `J` sum. -/
theorem zigzagLinearFactor_derivative_mul (d : ℕ) (a : ℝ) (F : ℝ[X]) :
    F * (zigzagLinearFactor a F).derivative =
      zigzagJ d F + C ((d : ℝ) + 3) * F ^ 2 +
        zigzagLinearFactor a F * F.derivative := by
  simp only [zigzagLinearFactor, zigzagOperator_apply, zigzagJ,
    derivative_sub, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_one, map_add, map_ofNat]
  norm_num [Polynomial.C_ofNat]
  ring

/-- At a zero of the linear insertion, its derivative has the old polynomial's sign. -/
theorem zigzagLinearFactor_eval_derivative_mul_pos (F : ℝ[X])
    (hF : F.Splits) (hdeg : 0 < F.natDegree)
    (hroots : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (a s : ℝ) (hFs : F.eval s ≠ 0)
    (hlinear : (zigzagLinearFactor a F).eval s = 0) :
    0 < F.eval s * (zigzagLinearFactor a F).derivative.eval s := by
  have h := congrArg (fun P : ℝ[X] => P.eval s)
    (zigzagLinearFactor_derivative_mul F.natDegree a F)
  simp only [eval_mul, eval_add, eval_C, eval_pow, hlinear, zero_mul, add_zero] at h
  have hJ := zigzagJ_eval_pos_of_splits F hF hdeg hroots s hFs
  have hsq : 0 ≤ ((F.natDegree : ℝ) + 3) * (F.eval s) ^ 2 := by positivity
  linarith

/-- The conjugate-pair insertion has the opposite sign to the old polynomial
at an interior zero of its linear insertion. -/
theorem zigzagQuadraticFactor_eval_mul_neg_of_splits (F : ℝ[X])
    (hF : F.Splits) (hdeg : 4 ≤ F.natDegree)
    (hroots : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (a b s : ℝ) (hdisk : a ^ 2 + b ^ 2 ≤ 13 / 3)
    (hs : -1 < s ∧ s < 1) (hFs : F.eval s ≠ 0)
    (hlinear : (zigzagLinearFactor a F).eval s = 0) :
    F.eval s * (zigzagQuadraticFactor a b F).eval s < 0 := by
  apply zigzag_quadratic_eval_mul_neg F.natDegree a b s F
  · nlinarith [mul_pos (show 0 < 1 - s by linarith [hs.2])
      (show 0 < 1 + s by linarith [hs.1])]
  · exact zigzagJ_eval_pos_of_splits F hF (by lia) hroots s hFs
  · exact zigzagK_eval_nonneg_of_splits F hF s
  · have hd : (4 : ℝ) ≤ F.natDegree := by exact_mod_cast hdeg
    have hgap : 0 ≤ ((F.natDegree : ℝ) + 2) *
        (13 / 3 - (a ^ 2 + b ^ 2)) := mul_nonneg (by positivity) (by linarith)
    have hsq : 0 ≤ ((F.natDegree : ℝ) + 3) * (a - s) ^ 2 := by positivity
    nlinarith
  · exact hlinear

end RealRooted.IntervalDifferential
