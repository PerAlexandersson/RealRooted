/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import RealRooted.Mathlib.Analysis.Complex.Contour.Winding.Number.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Original source: `TauCeti/Analysis/Contour/Winding/Number/Circle.lean`,
in TauCetiProject/TauCeti@5f291f7 (Apache-2.0).

# Winding numbers of circles

This file contains the portion of Tau Ceti's circle winding API needed by the cycle acceptance
examples: the winding number is one inside a positively oriented circle and zero outside it.
-/

public section

noncomputable section

open Complex Metric

namespace Complex.Contour

/-- The Cauchy-kernel integral around a circle vanishes when its pole is outside the circle. -/
theorem circleIntegral_sub_inv_eq_zero_of_lt_dist {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : R < dist w c) : (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
  have hdiff : DifferentiableOn ℂ (fun z => (z - w)⁻¹) ({w}ᶜ) := by
    intro z hz
    have hzw : z ≠ w := by simpa using hz
    exact ((differentiableAt_id.sub_const w).inv
      (sub_ne_zero.mpr hzw)).differentiableWithinAt
  have hsub : closedBall c R ⊆ ({w}ᶜ) := by
    intro z hz
    have hzc : dist z c ≤ R := mem_closedBall.mp hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact absurd hzc (not_le.mpr hw)
  exact (hdiff.diffContOnCl_ball hsub).circleIntegral_eq_zero hR

/-- Away from a circle, its winding number is the normalized Cauchy-kernel circle integral. -/
theorem windingNumber_circleMap_eq_circleIntegral {c w : ℂ} {R : ℝ}
    (havoid : ∀ θ, circleMap c R θ ≠ w) :
    windingNumber (circleMap c R) 0 (2 * Real.pi) w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C(c, R), (z - w)⁻¹ := by
  have hcont : ContinuousOn (circleMap c R) (Set.uIcc 0 (2 * Real.pi)) :=
    (continuous_circleMap c R).continuousOn
  have hderiv : Continuous (fun θ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hint : IntervalIntegrable
      (fun t => (circleMap c R t - w)⁻¹ * deriv (circleMap c R) t)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    intervalIntegrable_inv_sub_mul_deriv hcont (fun t _ => havoid t)
      (hderiv.intervalIntegrable _ _)
  rw [windingNumber_eq_integral_of_avoidance hcont (fun t _ => havoid t) hint]
  congr 1
  simp only [circleIntegral, smul_eq_mul]
  exact intervalIntegral.integral_congr fun θ _ => mul_comm _ _

/-- A positively oriented circle has winding number one about every point in its interior. -/
theorem windingNumber_circleMap_eq_one_of_dist_lt {c w : ℂ} {R : ℝ}
    (hw : dist w c < R) :
    windingNumber (circleMap c R) 0 (2 * Real.pi) w = 1 := by
  have havoid : ∀ θ, circleMap c R θ ≠ w :=
    fun θ => circleMap_ne_mem_ball (mem_ball.mpr hw) θ
  rw [windingNumber_circleMap_eq_circleIntegral havoid,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball.mpr hw)]
  exact inv_mul_cancel₀ Complex.two_pi_I_ne_zero

/-- A positively oriented circle has winding number zero about every exterior point. -/
theorem windingNumber_circleMap_eq_zero_of_lt_dist {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : R < dist w c) :
    windingNumber (circleMap c R) 0 (2 * Real.pi) w = 0 := by
  have havoid : ∀ θ, circleMap c R θ ≠ w := fun θ =>
    ne_of_mem_of_not_mem (circleMap_mem_closedBall c hR θ)
      (fun h => absurd (mem_closedBall.mp h) (not_le.mpr hw))
  rw [windingNumber_circleMap_eq_circleIntegral havoid,
    circleIntegral_sub_inv_eq_zero_of_lt_dist hR hw, mul_zero]

end Complex.Contour

end
