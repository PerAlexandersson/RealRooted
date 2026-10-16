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

public noncomputable section

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

/-- At each interior root of the linear insertion, the quadratic insertion
has the opposite sign to its derivative. This is the strict sign input for
the interval root criterion in Appendix C.2. -/
theorem zigzagQuadraticFactor_eval_derivative_mul_neg (F : ℝ[X])
    (hF : F.Splits) (hdeg : 4 ≤ F.natDegree)
    (hroots : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (a b s : ℝ) (hdisk : a ^ 2 + b ^ 2 ≤ 13 / 3)
    (hs : -1 < s ∧ s < 1) (hFs : F.eval s ≠ 0)
    (hlinear : (zigzagLinearFactor a F).eval s = 0) :
    (zigzagQuadraticFactor a b F).eval s *
      (zigzagLinearFactor a F).derivative.eval s < 0 := by
  have hpos := zigzagLinearFactor_eval_derivative_mul_pos F hF (by lia)
    hroots a s hFs hlinear
  have hneg := zigzagQuadraticFactor_eval_mul_neg_of_splits F hF hdeg
    hroots a b s hdisk hs hFs hlinear
  rcases lt_or_gt_of_ne hFs with h | h
  · exact mul_neg_of_pos_of_neg (pos_of_mul_neg_right hneg (le_of_lt h))
      (neg_of_mul_pos_right hpos (le_of_lt h))
  · exact mul_neg_of_neg_of_pos (neg_of_mul_neg_right hneg (le_of_lt h))
      (pos_of_mul_pos_right hpos (le_of_lt h))

/-- The quadratic and linear insertions have the endpoint signs required
by the strict interval root criterion. -/
theorem zigzagQuadraticFactor_endpoint_signs (F : ℝ[X]) (hF : F ≠ 0)
    (hroots : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (a b : ℝ) (hdisk : a ^ 2 + b ^ 2 ≤ 13 / 3) :
    (zigzagQuadraticFactor a b F).eval (-1) *
        (zigzagLinearFactor a F).eval (-1) < 0 ∧
      0 < (zigzagQuadraticFactor a b F).eval 1 *
        (zigzagLinearFactor a F).eval 1 := by
  have ha : -3 < a ∧ a < 3 := by
    constructor <;> nlinarith [sq_nonneg b]
  have hleft : F.eval (-1) ≠ 0 := by
    intro h
    have hr := hroots (-1) ((mem_roots hF).mpr h)
    linarith [hr.1]
  have hright : F.eval 1 ≠ 0 := by
    intro h
    have hr := hroots 1 ((mem_roots hF).mpr h)
    linarith [hr.2]
  have hplus : 0 < 3 + a := by linarith [ha.1]
  have hminus : 0 < 3 - a := by linarith [ha.2]
  have hplus2 : 0 < (3 + a) ^ 2 + b ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hplus) (sq_nonneg b)
  have hminus2 : 0 < (3 - a) ^ 2 + b ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hminus) (sq_nonneg b)
  rw [zigzagQuadraticFactor_eval_neg_one, zigzagLinearFactor_eval_neg_one,
    zigzagQuadraticFactor_eval_one, zigzagLinearFactor_eval_one]
  constructor
  · have h := mul_pos (mul_pos hplus2 hplus) (sq_pos_of_ne_zero hleft)
    nlinarith
  · have h := mul_pos (mul_pos hminus2 hminus) (sq_pos_of_ne_zero hright)
    nlinarith

/-- Inserting a conjugate pair in the closed squared-radius `13/3` disk
preserves simple roots in `(-1,1)` when the input degree is at least four.
This is Appendix C.2 of the zig-zag transfer argument. -/
theorem zigzagQuadraticFactor_roots (F : ℝ[X]) (a b : ℝ)
    (hF : F.Splits) (hnd : F.roots.Nodup) (hdeg : 4 ≤ F.natDegree)
    (hinside : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hdisk : a ^ 2 + b ^ 2 ≤ 13 / 3) :
    (zigzagQuadraticFactor a b F).Splits ∧
      (zigzagQuadraticFactor a b F).roots.Nodup ∧
      ∀ r ∈ (zigzagQuadraticFactor a b F).roots, -1 < r ∧ r < 1 := by
  have hF0 : F ≠ 0 := ne_zero_of_natDegree_gt (show 0 < F.natDegree by lia)
  have ha : -3 < a ∧ a < 3 := by
    constructor <;> nlinarith [sq_nonneg b]
  obtain ⟨hG, hGnd, hGinside⟩ :=
    zigzagLinearFactor_roots F a hF hF0 hnd hinside ha.1 ha.2
  have hG0 := zigzagLinearFactor_ne_zero a F hF0
  apply splits_nodup_interval_of_root_derivative_signs hG hG0 hGnd hGinside
  · rw [zigzagQuadraticFactor_natDegree a b F hF0,
      zigzagLinearFactor_natDegree a F hF0]
  · intro s hs
    have hlinear := (mem_roots hG0).mp hs
    exact zigzagQuadraticFactor_eval_derivative_mul_neg F hF hdeg hinside
      a b s hdisk (hGinside s hs)
      (zigzagLinearFactor_eval_base_ne_zero hF hF0 hnd hinside a s hlinear) hlinear
  · exact (zigzagQuadraticFactor_endpoint_signs F hF0 hinside a b hdisk).1
  · exact (zigzagQuadraticFactor_endpoint_signs F hF0 hinside a b hdisk).2

end RealRooted.IntervalDifferential
