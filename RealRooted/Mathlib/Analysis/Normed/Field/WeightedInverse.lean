/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Weighted inverse sums away from zero

When the real parameters stay away from zero, summability with the bounded
weight `1 / (1 + r^2)` implies inverse-square summability and convergence of the
linear correction used in genus-one canonical products.
-/

public section

/-- Away from zero, a summable sequence of nonnegative weights divided by
`1 + r^2` remains summable when divided by `r^2`. -/
theorem Summable.div_sq_of_abs_ge {ι : Type*} {a r : ι → ℝ} {δ : ℝ}
    (hs : Summable (fun i => a i / (1 + r i ^ 2))) (ha : ∀ i, 0 ≤ a i)
    (hδ : 0 < δ) (hr : ∀ i, δ ≤ |r i|) :
    Summable (fun i => a i / r i ^ 2) := by
  apply Summable.of_nonneg_of_le (fun i => div_nonneg (ha i) (sq_nonneg _))
    (f := fun i => (1 + 1 / δ ^ 2) * (a i / (1 + r i ^ 2)))
  · intro i
    have hsq : δ ^ 2 ≤ r i ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hδ.le (hr i) 2
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have hrsq : 0 < r i ^ 2 := hδsq.trans_le hsq
    have hp : 1 + r i ^ 2 ≠ 0 := by positivity
    have hratio : (1 + r i ^ 2) / r i ^ 2 ≤ 1 + 1 / δ ^ 2 := by
      rw [add_div, div_self hrsq.ne']
      linarith [one_div_le_one_div_of_le hδsq hsq]
    calc
      a i / r i ^ 2 = (a i / (1 + r i ^ 2)) * ((1 + r i ^ 2) / r i ^ 2) := by
        field_simp
      _ ≤ (a i / (1 + r i ^ 2)) * (1 + 1 / δ ^ 2) :=
        mul_le_mul_of_nonneg_left hratio (div_nonneg (ha i) (by positivity))
      _ = _ := mul_comm _ _
  · exact hs.mul_left _

/-- The signed linear correction in a genus-one product converges when its real
parameters stay away from zero and the corresponding finite-measure weights sum. -/
theorem Summable.div_mul_one_add_sq_of_abs_ge {ι : Type*} {a r : ι → ℝ} {δ : ℝ}
    (hs : Summable (fun i => a i / (1 + r i ^ 2))) (ha : ∀ i, 0 ≤ a i)
    (hδ : 0 < δ) (hr : ∀ i, δ ≤ |r i|) :
    Summable (fun i => a i / (r i * (1 + r i ^ 2))) := by
  apply (hs.mul_left (1 / δ)).of_norm_bounded
  intro i
  have habs : 0 < |r i| := hδ.trans_le (hr i)
  have hp : 0 < 1 + r i ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (ha i), abs_mul, abs_of_pos hp]
  calc
    a i / (|r i| * (1 + r i ^ 2)) =
        (a i / (1 + r i ^ 2)) * (1 / |r i|) := by field_simp
    _ ≤ (a i / (1 + r i ^ 2)) * (1 / δ) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hδ (hr i))
        (div_nonneg (ha i) hp.le)
    _ = _ := mul_comm _ _
