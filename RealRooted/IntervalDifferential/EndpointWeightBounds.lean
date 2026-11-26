/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.EndpointWeight
import RealRooted.Interlacing.SecondOrderPreservation
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Bounds for starting and continuing interval insertion

These are the two estimates in Lemma 1 of the unpublished structural
long-cycle descent notes. The shifted test polynomial gives the larger disk in the revised argument.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- Root distances in the unit interval give a degree-weighted lower bound
for the Laguerre expression. -/
theorem interval_laguerre_lower_bound (F : ℝ[X]) (hF : F.Splits)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1) (s : ℝ) (hFs : F.eval s ≠ 0) :
    (F.natDegree : ℝ) * (1 - |s|) ^ 2 * F.eval s ^ 2 ≤
      (1 - s ^ 2) ^ 2 *
        (F.derivative.eval s ^ 2 - F.eval s * F.derivative.derivative.eval s) := by
  have hb (r : ℝ) (hr : r ∈ F.roots) :
      (1 - |s|) ^ 2 ≤ (1 - s ^ 2) ^ 2 * (s - r)⁻¹ ^ 2 := by
    have hd : s - r ≠ 0 := by
      intro hz
      have hF0 : F ≠ 0 := by intro hz; simp [hz] at hFs
      exact hFs (sub_eq_zero.mp hz ▸ (mem_roots hF0).mp hr)
    have ha : |s - r| ≤ 1 + |s| := by
      have hrabs : |r| < 1 := abs_lt.mpr (hi r hr)
      linarith [abs_sub s r]
    have hsq : (s - r) ^ 2 ≤ (1 + |s|) ^ 2 := by
      nlinarith [sq_abs (s - r), abs_nonneg (s - r), abs_nonneg s]
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (1 - |s|))
    have heq : (1 - |s|) ^ 2 * (1 + |s|) ^ 2 = (1 - s ^ 2) ^ 2 := by
      calc
        _ = (1 - |s| ^ 2) ^ 2 := by ring
        _ = _ := by rw [sq_abs]
    have hb := (le_div_iff₀ (sq_pos_of_ne_zero hd)).mpr (hmul.trans_eq heq)
    simpa only [div_eq_mul_inv, inv_pow] using hb
  have hs := Multiset.sum_map_le_sum_map (s := F.roots)
    (fun _ : ℝ => (1 - |s|) ^ 2)
    (fun r : ℝ => (1 - s ^ 2) ^ 2 * (s - r)⁻¹ ^ 2) hb
  simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    Multiset.sum_map_mul_left] at hs
  rw [← hF.natDegree_eq_card_roots] at hs
  have he := laguerre_eval_eq_eval_sq_mul_rootSumSq_of_splits hF hFs
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (F.eval s))]

/-- The uniform threshold obtained by testing at a shifted linear insertion. -/
def intervalInsertionThreshold (c : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  d + c - ((d : ℝ) + |u|) ^ 2 / ((d : ℝ) + c)

/-- The root-distance bound and completion of the square give the shifted
quadratic sign criterion for every positive endpoint weight. -/
theorem intervalQuadraticFactor_shift_eval_mul_neg (c a b u s : ℝ) (F : ℝ[X])
    (hc : 0 < c) (hF : F.Splits) (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hFs : F.eval s ≠ 0)
    (hpair : (a - u) ^ 2 + b ^ 2 < intervalInsertionThreshold c F.natDegree u)
    (hG : (intervalLinearFactor c u F).eval s = 0) :
    F.eval s * (intervalQuadraticFactor c a b F).eval s < 0 := by
  have hl := interval_laguerre_lower_bound F hF hi s hFs
  have hd : 0 < (F.natDegree : ℝ) + c := by positivity
  have he := intervalQuadraticFactor_eval_identity c a b u s F hG
  have ha : u * s ≤ |u| * |s| := by simpa only [abs_mul] using le_abs_self (u * s)
  have ham := mul_le_mul_of_nonneg_left ha hd.le
  have hdiv := div_mul_cancel₀ (((F.natDegree : ℝ) + |u|) ^ 2) hd.ne'
  unfold intervalInsertionThreshold at hpair
  have hgap := mul_pos hd (sub_pos.mpr hpair)
  have hcoef : 0 < (F.natDegree : ℝ) * (1 - |s|) ^ 2 +
      c + c * s ^ 2 - 2 * u * s - ((a - u) ^ 2 + b ^ 2) := by
    have hsq := sq_nonneg (((F.natDegree : ℝ) + c) * |s| - (F.natDegree + |u|))
    rw [← sq_abs s]
    by_contra hn
    have hmul := mul_nonpos_of_nonneg_of_nonpos hd.le (le_of_not_gt hn)
    nlinarith [hdiv, hgap, ham]
  have hp := mul_pos hcoef (sq_pos_of_ne_zero hFs)
  nlinarith [he, hl]

/-- Shifted linear test points give a reusable quadratic insertion criterion. -/
theorem intervalQuadraticFactor_shift_roots (c a b u : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1) (hu : |u| < c) (hb : b ≠ 0)
    (hpair : (a - u) ^ 2 + b ^ 2 < intervalInsertionThreshold c F.natDegree u) :
    (intervalQuadraticFactor c a b F).Splits ∧
      (intervalQuadraticFactor c a b F).roots.Nodup ∧
      ∀ r ∈ (intervalQuadraticFactor c a b F).roots, -1 < r ∧ r < 1 := by
  apply intervalQuadraticFactor_roots_of_eval_mul_neg c a b u F hc hF hF0 hnd hi
    (abs_lt.mp hu)
  · constructor <;> nlinarith [sq_pos_of_ne_zero hb, sq_nonneg (c + a), sq_nonneg (c - a)]
  · intro s _ hs hg
    exact intervalQuadraticFactor_shift_eval_mul_neg c a b u s F hc hF hi hs hpair hg

/-- Every pair in the squared-radius `25/4` disk is admissible after degree six. -/
theorem intervalInsertionThreshold_six {d : ℕ} (hd : 6 ≤ d) :
    (25 / 4 : ℝ) < intervalInsertionThreshold 4 d 0 := by
  have hdr : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < (d : ℝ) + 4 := by positivity
  unfold intervalInsertionThreshold
  rw [abs_zero, add_zero]
  have he := div_mul_cancel₀ ((d : ℝ) ^ 2) hp.ne'
  by_contra hn
  have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hp.le
  nlinarith

/-- The six rational starting inequalities from the revised structural note. -/
theorem intervalInsertionThreshold_small {d : ℕ} (hd : d < 6) (a b : ℝ)
    (hdisk : a ^ 2 + b ^ 2 ≤ 25 / 4)
    (hmoment : -(2 + (25 / 16 : ℝ) * d) / (15 - d) ≤ (a ^ 2 - b ^ 2) / 4) :
    ∃ u : ℝ, |u| < 4 ∧
      (a - u) ^ 2 + b ^ 2 < intervalInsertionThreshold 4 d u := by
  let v : ℝ := (6 - (d : ℝ)) / 4
  have hdR : (d : ℝ) < 6 := by exact_mod_cast hd
  have hv : 0 < v := by dsimp [v]; linarith
  have hv4 : v < 4 := by dsimp [v]; have h := Nat.cast_nonneg (α := ℝ) d; linarith
  have hmain : (|a| - v) ^ 2 + b ^ 2 < intervalInsertionThreshold 4 d v := by
    by_contra hnot
    have hfail := le_of_not_gt hnot
    have hA : |a| ≤ (25 / 4 + v ^ 2 - intervalInsertionThreshold 4 d v) / (2 * v) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * v)).mpr
      nlinarith [sq_abs a]
    have hconvex := mul_nonneg (abs_nonneg a) (sub_nonneg.mpr hA)
    dsimp only [v] at hA hconvex hfail
    interval_cases d <;> norm_num only [v, intervalInsertionThreshold] at * <;>
      nlinarith [sq_abs a]
  by_cases ha : 0 ≤ a
  · refine ⟨v, by simpa only [abs_of_pos hv] using hv4, ?_⟩
    simpa only [abs_of_nonneg ha] using hmain
  · refine ⟨-v, ?_, ?_⟩
    · simpa only [abs_neg, abs_of_pos hv] using hv4
    · have hab : |a| = -a := abs_of_neg (lt_of_not_ge ha)
      have hth : intervalInsertionThreshold 4 d (-v) = intervalInsertionThreshold 4 d v := by
        simp only [intervalInsertionThreshold, abs_neg]
      rw [hth]
      rw [hab] at hmain
      nlinarith

end RealRooted.IntervalDifferential
