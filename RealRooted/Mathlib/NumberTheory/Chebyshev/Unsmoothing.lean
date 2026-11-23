/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.PrimitiveBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unsmoothing the Chebyshev integral and removing prime powers

The real-valued function `psiIntegralError` subtracts the quadratic main term
from the integral of `psi`. Bounds for its forward and backward differences
at step `sqrt x` imply pointwise bounds for `psi x - x`. Mathlib's unconditional
bound `psi - theta = O(sqrt x)` then transfers the error to `theta`.

The finite-difference bounds remain explicit hypotheses throughout this file.
These are unconditional reduction theorems, not RH error estimates by
themselves. The RH application must supply those bounds from the explicit
formula, the zero contribution, and the left-line remainder.
-/

public section

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Chebyshev

/-- The first integrated Chebyshev error after removing the quadratic main term. -/
@[expose]
noncomputable def psiIntegralError (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x, psi t) - x ^ 2 / 2

/-- At large arguments the logarithmic-square weight absorbs the square-root smoothing error. -/
private theorem sqrt_le_sqrt_mul_log_sq {x : ℝ} (hx : 25 ≤ x) :
    Real.sqrt x ≤ Real.sqrt x * Real.log x ^ 2 := by
  have hlog : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_three])
  have hsq : 1 ≤ Real.log x ^ 2 := by nlinarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg x)

/-- Square-root finite-difference bounds for the integrated error recover the RH-scale
pointwise error for `psi`, with explicit constant `C + 1`. -/
theorem abs_psi_sub_le_of_psiIntegralError_bounds {x C : ℝ} (hx : 25 ≤ x)
    (hback : |(psiIntegralError x - psiIntegralError (x - Real.sqrt x)) / Real.sqrt x| ≤
      C * (Real.sqrt x * Real.log x ^ 2))
    (hforward : |(psiIntegralError (x + Real.sqrt x) - psiIntegralError x) / Real.sqrt x| ≤
      C * (Real.sqrt x * Real.log x ^ 2)) :
    |psi x - x| ≤ (C + 1) * (Real.sqrt x * Real.log x ^ 2) := by
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have h := psi_mono.abs_sub_le_of_integral_sub_quadratic_bounds hsqrt hback hforward
  have hsmall : Real.sqrt x / 2 ≤ Real.sqrt x * Real.log x ^ 2 :=
    (by linarith [Real.sqrt_nonneg x] : Real.sqrt x / 2 ≤ Real.sqrt x).trans
      (sqrt_le_sqrt_mul_log_sq hx)
  calc
    |psi x - x| ≤ Real.sqrt x / 2 + C * (Real.sqrt x * Real.log x ^ 2) := h
    _ ≤ (Real.sqrt x * Real.log x ^ 2) + C * (Real.sqrt x * Real.log x ^ 2) :=
      add_le_add hsmall le_rfl
    _ = (C + 1) * (Real.sqrt x * Real.log x ^ 2) := by ring

/-- Removing prime powers enlarges any `sqrt(x) log(x)^2` bound for `psi - id`
by one fixed unconditional constant. -/
theorem exists_abs_theta_sub_le_of_abs_psi_sub_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x C : ℝ, 25 ≤ x →
      |psi x - x| ≤ C * (Real.sqrt x * Real.log x ^ 2) →
      |theta x - x| ≤ (C + D) * (Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨D, hD⟩ := psi_sub_theta_le_mul_sqrt
  have hD₀ : 0 ≤ D := by simpa using hD 1
  refine ⟨D, hD₀, fun x C hx hpsi ↦ ?_⟩
  calc
    |theta x - x| ≤ |theta x - psi x| + |psi x - x| := abs_sub_le _ _ _
    _ = (psi x - theta x) + |psi x - x| := by
      rw [abs_of_nonpos (sub_nonpos.mpr (theta_le_psi x))]
      ring
    _ ≤ D * Real.sqrt x + C * (Real.sqrt x * Real.log x ^ 2) :=
      add_le_add (hD x) hpsi
    _ ≤ D * (Real.sqrt x * Real.log x ^ 2) + C * (Real.sqrt x * Real.log x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (sqrt_le_sqrt_mul_log_sq hx) hD₀) le_rfl
    _ = (C + D) * (Real.sqrt x * Real.log x ^ 2) := by ring

/-- Uniform bounds for the two integrated-error differences yield a shared positive
pointwise error constant for both Chebyshev functions. -/
theorem exists_abs_psi_theta_sub_le_of_psiIntegralError_bounds {C : ℝ} (hC : 0 ≤ C)
    (hback : ∀ x : ℝ, 25 ≤ x →
      |(psiIntegralError x - psiIntegralError (x - Real.sqrt x)) / Real.sqrt x| ≤
        C * (Real.sqrt x * Real.log x ^ 2))
    (hforward : ∀ x : ℝ, 25 ≤ x →
      |(psiIntegralError (x + Real.sqrt x) - psiIntegralError x) / Real.sqrt x| ≤
        C * (Real.sqrt x * Real.log x ^ 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 25 ≤ x →
      |psi x - x| ≤ K * (Real.sqrt x * Real.log x ^ 2) ∧
      |theta x - x| ≤ K * (Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨D, hD, htransfer⟩ := exists_abs_theta_sub_le_of_abs_psi_sub_le
  refine ⟨C + 1 + D, by linarith, fun x hx ↦ ?_⟩
  have hpsi := abs_psi_sub_le_of_psiIntegralError_bounds hx (hback x hx) (hforward x hx)
  refine ⟨hpsi.trans ?_, htransfer x (C + 1) hx hpsi⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Eventual finite-difference bounds imply the RH-scale `IsBigO` bound for `psi - id`. -/
theorem isBigO_psi_sub_id_of_psiIntegralError_bounds {C : ℝ}
    (hback : ∀ᶠ x : ℝ in atTop,
      |(psiIntegralError x - psiIntegralError (x - Real.sqrt x)) / Real.sqrt x| ≤
        C * (Real.sqrt x * Real.log x ^ 2))
    (hforward : ∀ᶠ x : ℝ in atTop,
      |(psiIntegralError (x + Real.sqrt x) - psiIntegralError x) / Real.sqrt x| ≤
        C * (Real.sqrt x * Real.log x ^ 2)) :
    (fun x : ℝ ↦ psi x - x) =O[atTop] (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2) := by
  apply IsBigO.of_bound (C + 1)
  filter_upwards [hback, hforward, eventually_ge_atTop (25 : ℝ)] with x hb hf hx
  have hw : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hw] using
    abs_psi_sub_le_of_psiIntegralError_bounds hx hb hf

/-- The RH-scale error bound for `psi - id` transfers unconditionally to `theta - id`. -/
theorem isBigO_theta_sub_id_of_isBigO_psi_sub_id
    (hpsi : (fun x : ℝ ↦ psi x - x) =O[atTop]
      (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2)) :
    (fun x : ℝ ↦ theta x - x) =O[atTop]
      (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp hpsi
  obtain ⟨D, _, htransfer⟩ := exists_abs_theta_sub_le_of_abs_psi_sub_le
  apply IsBigO.of_bound (C + D)
  filter_upwards [hC, eventually_ge_atTop (25 : ℝ)] with x hx hx25
  have hw : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by positivity
  have hpsi' : |psi x - x| ≤ C * (Real.sqrt x * Real.log x ^ 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hw] using hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hw] using htransfer x C hx25 hpsi'

/-- Eventual bounds on the integrated `psi` error suffice for the corresponding `theta` estimate. -/
theorem isBigO_theta_sub_id_of_psiIntegralError_bounds {C : ℝ}
    (hback : ∀ᶠ x : ℝ in atTop,
      |(psiIntegralError x - psiIntegralError (x - Real.sqrt x)) / Real.sqrt x| ≤
        C * (Real.sqrt x * Real.log x ^ 2))
    (hforward : ∀ᶠ x : ℝ in atTop,
      |(psiIntegralError (x + Real.sqrt x) - psiIntegralError x) / Real.sqrt x| ≤
        C * (Real.sqrt x * Real.log x ^ 2)) :
    (fun x : ℝ ↦ theta x - x) =O[atTop]
      (fun x : ℝ ↦ Real.sqrt x * Real.log x ^ 2) :=
  isBigO_theta_sub_id_of_isBigO_psi_sub_id
    (isBigO_psi_sub_id_of_psiIntegralError_bounds hback hforward)

end Chebyshev
