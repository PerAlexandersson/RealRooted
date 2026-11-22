/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Arbitrarily small quadratic exponential bounds

A continuous function of growth order strictly below two admits a global bound
by a constant times `exp (ε ‖z‖²)` for every positive `ε`. This is the quantitative
growth input for entire heat-operator convergence.
-/

public section

open Complex Filter Asymptotics Bornology Metric Topology

namespace TauCeti

/-- An eventual Gaussian exponential bound for a continuous function can be
made global by increasing its constant. -/
private theorem exists_global_quadratic_bound {f : ℂ → ℂ} (hf : Continuous f)
    (h : f =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ 2)) :
    ∃ C > 0, ∀ z, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hbound.bound
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C B, lt_of_lt_of_le hC (le_max_left _ _), fun z => ?_⟩
  by_cases hz : R ≤ ‖z‖
  · have hzbound : ‖f z‖ ≤ C * Real.exp (‖z‖ ^ 2) := by
      simpa only [Real.norm_eq_abs, Real.abs_exp] using hR hz
    exact hzbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hsmall : ‖f z‖ ≤ B := hB z (by simpa using (le_of_not_ge hz))
    exact hsmall.trans ((le_max_right C B).trans
      (le_mul_of_one_le_right (le_max_left C B |>.trans' hC.le)
        (Real.one_le_exp (sq_nonneg _))))

/-- Every continuous function of order below two has a global quadratic
exponential bound with arbitrarily small positive quadratic coefficient. -/
theorem OrderLE.exists_norm_le_mul_exp_sq {f : ℂ → ℂ} {ρ : ℝ}
    (h : OrderLE f ρ) (hf : Continuous f) (hρ : ρ < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ z, ‖f z‖ ≤ C * Real.exp (ε * ‖z‖ ^ 2) := by
  let a : ℂ := (Real.sqrt ε : ℂ)
  have ha : a ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε).ne'
  have hg : Continuous (fun z : ℂ => f (a⁻¹ * z)) := hf.comp (by fun_prop)
  have ho : OrderLE (fun z : ℂ => f (a⁻¹ * z)) ρ := by
    simpa only [add_zero] using h.comp_mul_add a⁻¹ 0
  have hb : (fun z : ℂ => f (a⁻¹ * z)) =O[cobounded ℂ]
      fun z => Real.exp (‖z‖ ^ 2) := by
    simpa only [Real.rpow_two] using ho.isBigO hρ
  obtain ⟨C, hC, hbound⟩ := exists_global_quadratic_bound hg hb
  refine ⟨C, hC, fun z => ?_⟩
  have hz := hbound (a * z)
  rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul, norm_mul, mul_pow] at hz
  have hnorm : ‖a‖ ^ 2 = ε := by
    simp only [a, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt hε.le
  simpa only [hnorm] using hz

end TauCeti
