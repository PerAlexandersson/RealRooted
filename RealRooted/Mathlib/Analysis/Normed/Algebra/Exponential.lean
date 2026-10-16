/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Exponentials of continuous linear endomorphisms

This file records the injectivity of the exponential of a bounded linear
endomorphism. It is the nonvanishing step in finite-dimensional semigroup
arguments.
-/

public noncomputable section

namespace ContinuousLinearMap

/-- The exponential of a continuous linear endomorphism is injective. -/
theorem injective_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) :
    Function.Injective (fun x => NormedSpace.exp T x) := by
  intro x y hxy
  have hinv : NormedSpace.exp (-T) * NormedSpace.exp T = 1 := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball
      (𝕂 := ℝ) (Commute.refl T).neg_left
      ((NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸
        edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸
        edist_lt_top _ _)]
    simp
  calc
    x = (1 : E →L[ℝ] E) x := by simp
    _ = (NormedSpace.exp (-T) * NormedSpace.exp T) x := by rw [hinv]
    _ = NormedSpace.exp (-T) (NormedSpace.exp T x) := by
      rw [mul_apply_eq_comp]
    _ = NormedSpace.exp (-T) (NormedSpace.exp T y) := by
      exact congrArg (fun z => NormedSpace.exp (-T) z) hxy
    _ = (NormedSpace.exp (-T) * NormedSpace.exp T) y := by
      rw [mul_apply_eq_comp]
    _ = (1 : E →L[ℝ] E) y := by rw [hinv]
    _ = y := by simp

end ContinuousLinearMap

