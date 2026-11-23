/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Complex.RootsOfUnity.Descent

/-!
# Growth order under square descent

The principal square-root substitution divides a complex growth-order bound
by two. No analyticity or evenness assumption is needed for this estimate;
evenness is what makes the resulting descent entire in its applications.
-/

public section

open Complex Filter Bornology Asymptotics

namespace TauCeti

/-- Square descent halves any real growth-order bound. -/
theorem OrderLE.descendPow_two {f : ℂ → ℂ} {rho : ℝ} (hf : OrderLE f rho) :
    OrderLE (descendPow 2 f) (rho / 2) := by
  let root : ℂ → ℂ := fun z ↦ z ^ (2⁻¹ : ℂ)
  have hsq (z : ℂ) : ‖root z‖ ^ 2 = ‖z‖ := by
    rw [← norm_pow]
    exact congrArg norm (Complex.cpow_nat_inv_pow z (by norm_num : 2 ≠ 0))
  have ht : Tendsto root (cobounded ℂ) (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [eventually_cobounded_le_norm ((max R 0) ^ 2)] with z hz
    have := hsq z
    have := norm_nonneg (root z)
    have := le_max_left R 0
    have := le_max_right R 0
    nlinarith
  rw [orderLE_def]
  intro A hA
  have h := (hf.isBigO (show rho < 2 * A by linarith)).comp_tendsto ht
  change (fun z ↦ descendPow 2 f z) =O[cobounded ℂ] (fun z ↦ Real.exp (‖z‖ ^ A))
  have heq : (fun z ↦ descendPow 2 f z) = f ∘ root := by
    funext z
    exact descendPow_apply f z
  rw [heq]
  refine h.trans (IsBigO.of_bound 1 ?_)
  apply Eventually.of_forall
  intro z
  have hpow : ‖root z‖ ^ (2 * A) = ‖z‖ ^ A := by
    rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two, hsq]
  simp only [Function.comp_apply, Real.norm_eq_abs, Real.abs_exp, one_mul, hpow, le_refl]

end TauCeti
