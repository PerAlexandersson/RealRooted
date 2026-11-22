/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Global exponential power bounds above the growth order

Every positive exponent strictly above a continuous function's growth order
gives a global exponential power bound, with any prescribed positive constant
in the exponent. Compactness removes the exceptional bounded region.
-/

public section

open Complex Filter Asymptotics Bornology Metric Topology

namespace TauCeti

/-- An eventual exponential power bound can be made global for continuous functions. -/
private theorem exists_global_exponential_power_bound {f : ℂ → ℂ} (hf : Continuous f)
    (p : ℝ) (h : f =O[cobounded ℂ] fun z => Real.exp (‖z‖ ^ p)) :
    ∃ C > 0, ∀ z, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ p) := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hbound.bound
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C B, lt_of_lt_of_le hC (le_max_left _ _), fun z => ?_⟩
  by_cases hz : R ≤ ‖z‖
  · have hzbound : ‖f z‖ ≤ C * Real.exp (‖z‖ ^ p) := by
      simpa only [Real.norm_eq_abs, Real.abs_exp] using hR hz
    exact hzbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hsmall : ‖f z‖ ≤ B := hB z (by simpa using (le_of_not_ge hz))
    exact hsmall.trans ((le_max_right C B).trans
      (le_mul_of_one_le_right (le_max_left C B |>.trans' hC.le)
        (Real.one_le_exp (Real.rpow_nonneg (norm_nonneg _) _))))

/-- Above its growth order, a continuous function admits a global exponential
power bound with an arbitrarily small positive coefficient. -/
theorem OrderLE.exists_norm_le_mul_exp_rpow {f : ℂ → ℂ} {ρ p : ℝ}
    (h : OrderLE f ρ) (hf : Continuous f) (hp : 0 < p) (hρ : ρ < p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ z, ‖f z‖ ≤ C * Real.exp (ε * ‖z‖ ^ p) := by
  let a : ℂ := (ε ^ p⁻¹ : ℝ)
  have ha : a ≠ 0 := ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hε _).ne'
  have hg : Continuous (fun z : ℂ => f (a⁻¹ * z)) := hf.comp (by fun_prop)
  have ho : OrderLE (fun z : ℂ => f (a⁻¹ * z)) ρ := by
    simpa only [add_zero] using h.comp_mul_add a⁻¹ 0
  obtain ⟨C, hC, hbound⟩ := exists_global_exponential_power_bound hg p (ho.isBigO hρ)
  refine ⟨C, hC, fun z => ?_⟩
  have hz := hbound (a * z)
  rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at hz
  have hnorm : ‖a‖ ^ p = ε := by
    simp only [a, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hε.le _)]
    exact Real.rpow_inv_rpow hε.le hp.ne'
  simpa only [hnorm] using hz

end TauCeti
