/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import RealRooted.Mathlib.Analysis.Complex.Contour.Cycle.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Data.Set.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import RealRooted.Mathlib.Analysis.Complex.Contour.Cycle.HomologyCauchy
import RealRooted.Mathlib.Analysis.Complex.Contour.Winding.Number.Circle
import RealRooted.Mathlib.Analysis.Complex.Contour.Cycle.Winding

/-!
Original sources: `TauCeti/Analysis/Contour/Cycle/Basic.lean`,
`TauCeti/Analysis/Contour/Cycle/HomologyCauchy.lean`, and
`TauCeti/Analysis/Contour/Winding/Number/Circle.lean`, all in
TauCetiProject/TauCeti@5f291f7 (Apache-2.0).

# Acceptance examples for homology Cauchy on cycles

These examples check orientation, zero and integer multiples, and the essential cancellation of
two positively oriented circles in an annulus. Each circle has integral `2πi` against `z⁻¹`, but
their cycle difference is null-homologous in the annulus and has integral zero.
-/

@[expose] public section

noncomputable section

open Complex Metric Set

namespace Complex.Contour.Cycle

/-- The standard positively oriented circle of radius `R`, bundled as a closed piecewise-`C¹`
curve. -/
def circleCurve (R : ℝ) : PiecewiseC1ClosedCurve :=
  PiecewiseC1ClosedCurve.of (a := 0) (b := 2 * Real.pi) (circleMap 0 R)
    (IsPiecewiseC1On.of_contDiffOn (contDiff_circleMap 0 R).contDiffOn) (by
      simp [circleMap, Complex.exp_two_pi_mul_I])

/-- The one-generator cycle associated with the standard positively oriented circle. -/
def circleCycle (R : ℝ) : Cycle :=
  FreeAbelianGroup.of (circleCurve R)

/-- Reversing the orientation of a circle cycle negates every contour integral. -/
theorem integral_neg_circle (f : ℂ → ℂ) (R : ℝ) :
    integral f (-circleCycle R) = -integral f (circleCycle R) := by
  exact map_neg (integral f) (circleCycle R)

/-- The zero cycle has zero contour integral. -/
theorem integral_zero (f : ℂ → ℂ) : integral f (0 : Cycle) = 0 := by
  exact map_zero (integral f)

/-- Integer multiples of cycles scale their contour integrals by the same integer. -/
theorem integral_zsmul (f : ℂ → ℂ) (n : ℤ) (C : Cycle) :
    integral f (n • C) = n • integral f C := by
  exact map_zsmul (integral f) n C

/-- Integer multiples of cycles scale their winding numbers by the same integer. -/
theorem windingNumber_zsmul (z : ℂ) (n : ℤ) (C : Cycle) :
    windingNumber z (n • C) = n • windingNumber z C := by
  exact map_zsmul (windingNumber z) n C

/-- The annulus used in the whole-cycle cancellation example. -/
def acceptanceAnnulus : Set ℂ :=
  {z | (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 3}

/-- The acceptance annulus is open. -/
theorem isOpen_acceptanceAnnulus : IsOpen acceptanceAnnulus := by
  exact (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

/-- A circle whose radius is strictly between the annulus radii lies in the annulus. -/
theorem circleCycle_isIn_acceptanceAnnulus {R : ℝ} (hR0 : 0 ≤ R)
    (hRlo : 1 / 2 < R) (hRhi : R < 3) : IsIn (circleCycle R) acceptanceAnnulus := by
  rw [circleCycle, isIn_of_iff]
  intro t ht
  have ht' : t ∈ uIcc (0 : ℝ) (2 * Real.pi) := by
    simpa [circleCurve] using ht
  change (1 / 2 : ℝ) < ‖circleCurve R t‖ ∧ ‖circleCurve R t‖ < 3
  rw [circleCurve, PiecewiseC1ClosedCurve.of_apply _ _ _ ht', norm_circleMap_zero,
    abs_of_nonneg hR0]
  exact ⟨hRlo, hRhi⟩

/-- The bundled circle cycle has winding number one at every point inside the circle. -/
theorem windingNumber_circleCycle_eq_one_of_norm_lt {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) :
    windingNumber z (circleCycle R) = 1 := by
  rw [circleCycle, circleCurve, windingNumber_of_raw]
  exact windingNumber_circleMap_eq_one_of_dist_lt (by simpa using hz)

/-- The bundled circle cycle has winding number zero at every point outside the circle. -/
theorem windingNumber_circleCycle_eq_zero_of_lt_norm {R : ℝ} {z : ℂ} (hR : 0 ≤ R)
    (hz : R < ‖z‖) : windingNumber z (circleCycle R) = 0 := by
  rw [circleCycle, circleCurve, windingNumber_of_raw]
  exact windingNumber_circleMap_eq_zero_of_lt_dist hR (by simpa using hz)

/-- The difference between the radius-two and radius-one circles. -/
def annulusCircleDifference : Cycle :=
  circleCycle 2 - circleCycle 1

/-- The two-circle difference lies in the acceptance annulus. -/
theorem annulusCircleDifference_isIn : IsIn annulusCircleDifference acceptanceAnnulus := by
  rw [annulusCircleDifference, sub_eq_add_neg]
  exact (circleCycle_isIn_acceptanceAnnulus (R := 2) (by norm_num) (by norm_num)
    (by norm_num)).add (isIn_neg_iff.mpr
      (circleCycle_isIn_acceptanceAnnulus (R := 1) (by norm_num) (by norm_num)
        (by norm_num)))

/-- The two-circle difference is null-homologous in the annulus: its winding numbers cancel both
in the inner disc and outside the outer disc. -/
theorem annulusCircleDifference_isNullHomologous :
    IsNullHomologous annulusCircleDifference acceptanceAnnulus := by
  rw [isNullHomologous_iff]
  intro z hz
  simp only [acceptanceAnnulus, mem_ofPred_eq, not_and_or, not_lt] at hz
  rw [annulusCircleDifference, map_sub]
  rcases hz with hz | hz
  · rw [windingNumber_circleCycle_eq_one_of_norm_lt
        (lt_of_le_of_lt hz (by norm_num)),
      windingNumber_circleCycle_eq_one_of_norm_lt
        (lt_of_le_of_lt hz (by norm_num)), sub_self]
  · rw [windingNumber_circleCycle_eq_zero_of_lt_norm (by norm_num)
        (lt_of_lt_of_le (by norm_num) hz),
      windingNumber_circleCycle_eq_zero_of_lt_norm (by norm_num)
        (lt_of_lt_of_le (by norm_num) hz), sub_self]

/-- The inverse function is holomorphic throughout the acceptance annulus. -/
theorem differentiableOn_inv_acceptanceAnnulus :
    DifferentiableOn ℂ (fun z : ℂ => z⁻¹) acceptanceAnnulus := by
  intro z hz
  have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
  exact (hid.inv (norm_pos_iff.mp (lt_trans (by norm_num) hz.1))).differentiableWithinAt

/-- A positive-radius circle has integral `2πi` against `z⁻¹`. -/
theorem integral_inv_circleCycle {R : ℝ} (hR : 0 < R) :
    integral (fun z : ℂ => z⁻¹) (circleCycle R) =
      2 * (Real.pi : ℂ) * Complex.I := by
  have htrace : 0 ∉ trace (circleCycle R) := by
    rw [circleCycle, circleCurve, trace_of_raw]
    rintro ⟨t, ht, hzero⟩
    have hnorm := congrArg norm hzero
    rw [norm_circleMap_zero, abs_of_pos hR, norm_zero] at hnorm
    exact hR.ne' hnorm
  have hformula := windingNumber_eq_integral_of_not_mem_trace (circleCycle R) htrace
  rw [windingNumber_circleCycle_eq_one_of_norm_lt (by simpa using hR)] at hformula
  have hformula' :
      1 = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        integral (fun z : ℂ => z⁻¹) (circleCycle R) := by
    simpa using hformula
  have htwo : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := Complex.two_pi_I_ne_zero
  calc
    integral (fun z : ℂ => z⁻¹) (circleCycle R) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            integral (fun z : ℂ => z⁻¹) (circleCycle R)) := by
      rw [← mul_assoc, mul_inv_cancel₀ htwo, one_mul]
    _ = (2 * (Real.pi : ℂ) * Complex.I) * 1 := by
      rw [← hformula']
    _ = 2 * (Real.pi : ℂ) * Complex.I := mul_one _

/-- Each of the two positively oriented annulus circles has integral `2πi` against `z⁻¹`. -/
theorem integral_inv_annulus_circles :
    integral (fun z : ℂ => z⁻¹) (circleCycle 2) = 2 * (Real.pi : ℂ) * Complex.I ∧
      integral (fun z : ℂ => z⁻¹) (circleCycle 1) = 2 * (Real.pi : ℂ) * Complex.I := by
  exact ⟨integral_inv_circleCycle (by norm_num), integral_inv_circleCycle (by norm_num)⟩

/-- Although each annulus circle has integral `2πi` against `z⁻¹`, their cycle difference has
integral zero by the homology Cauchy theorem. -/
theorem integral_inv_annulusCircleDifference_eq_zero :
    integral (fun z : ℂ => z⁻¹) annulusCircleDifference = 0 := by
  exact integral_eq_zero_of_isNullHomologous isOpen_acceptanceAnnulus
    annulusCircleDifference_isIn differentiableOn_inv_acceptanceAnnulus
    annulusCircleDifference_isNullHomologous

end Complex.Contour.Cycle

end
