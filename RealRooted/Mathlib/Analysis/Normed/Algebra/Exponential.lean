/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponentials of continuous linear endomorphisms

This file records the injectivity of the exponential of a bounded linear
endomorphism, which is the nonvanishing step in finite-dimensional semigroup
arguments, and the action of the exponential on an eigenvector.
-/

public section

noncomputable section

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

/-- The exponential of a continuous linear endomorphism acts on an eigenvector `x` with eigenvalue
`c` by the scalar `Real.exp c`. -/
theorem exp_apply_of_eigenvector {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (x : E) (c : ℝ) (hx : T x = c • x) :
    NormedSpace.exp T x = Real.exp c • x := by
  have hpow : ∀ n : ℕ, (T ^ n) x = c ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx,
          pow_succ, smul_smul]
  have hs : Summable fun n : ℕ => (n.factorial : ℝ)⁻¹ • T ^ n := by
    simpa only [NormedSpace.expSeries_apply_eq] using
      NormedSpace.expSeries_summable T
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • T ^ n) x = _
  rw [show (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • T ^ n) x =
      ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ • T ^ n) x by
    simpa using (ContinuousLinearMap.apply ℝ E x).map_tsum hs]
  simp_rw [smul_apply, hpow, smul_smul]
  have hc : Summable fun n : ℕ => (n.factorial : ℝ)⁻¹ * c ^ n := by
    simpa [div_eq_mul_inv, mul_comm] using
      Real.summable_pow_div_factorial c
  rw [hc.tsum_smul_const x]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  congr

end ContinuousLinearMap
