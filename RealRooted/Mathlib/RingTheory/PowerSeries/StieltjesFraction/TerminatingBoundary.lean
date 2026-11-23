/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportParameters
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ActivePrefix

import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Coefficients

/-!
# A terminating boundary for lower-support parameters

The Dirac measure at a positive lower endpoint has the standard numerators
`(c,0,0,...)`. The existential parameter equations instead allow `(c,0,c,0,...)`.
These represent the same formal fraction. The standard all-zero tail cannot
satisfy the equations at every index. This distinguishes the main existential
support theorem from a literal all-index reading of arXiv:2404.12131v1, Remark 2.
-/

public section

open MeasureTheory

namespace PowerSeries

/-- The standard numerator sequence for a single atom. -/
@[expose] noncomputable def pointStieltjesNumerators (c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then c else 0

/-- The standard one-atom fraction is a single geometric-series step. -/
theorem stieltjesTail_point_eq (c : ℝ) :
    stieltjesTail (pointStieltjesNumerators c) 0 = stieltjesStep c 1 := by
  rw [stieltjesTail_eq_step, stieltjesTail_eq_step]
  simp [pointStieltjesNumerators]

/-- Coefficients of a one-step geometric fraction are powers of its numerator. -/
theorem coeff_stieltjesStep_one (c : ℝ) (n : ℕ) :
    coeff n (stieltjesStep c 1) = c ^ n :=
  coeff_stieltjesStep_one_eq_pow c n

/-- The standard one-atom fraction has the genuine moments of the Dirac measure at `c`. -/
theorem integral_dirac_eq_coeff_pointStieltjes (c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (Measure.dirac c) ∧
      (∫ x : ℝ, x ^ n ∂Measure.dirac c) =
        coeff n (stieltjesTail (pointStieltjesNumerators c) 0) := by
  refine ⟨integrable_dirac (by simp), ?_⟩
  rw [integral_dirac, stieltjesTail_point_eq, coeff_stieltjesStep_one]

/-- The geometric moment sequence has a representing measure at its lower endpoint. -/
theorem exists_moments_Ici_pointStieltjes (c : ℝ) :
    ∃ mu : Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) =
          coeff n (stieltjesTail (pointStieltjesNumerators c) 0) := by
  exact ⟨Measure.dirac c, by simp [ae_dirac_eq], integral_dirac_eq_coeff_pointStieltjes c⟩

/-- The nonstandard inactive tail supplied by zero parameters represents the
same one-atom fraction as the standard all-zero tail. -/
theorem stieltjesTail_point_eq_zero_parameters (c : ℝ) :
    stieltjesTail (pointStieltjesNumerators c) 0 =
      stieltjesTail (shiftedStieltjesNumerators c (fun _ => 0) (fun _ => 0)) 0 := by
  apply stieltjesTail_eq_of_terminating_prefix (N := 1) (by simp [pointStieltjesNumerators])
  intro n hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · simp [pointStieltjesNumerators, shiftedStieltjesNumerators]
  · simp [pointStieltjesNumerators, shiftedStieltjesNumerators]

/-- For a positive endpoint, no nonnegative parameters reproduce the standard
one-atom numerator sequence at every index. This is an inactive-tail obstruction. -/
theorem pointStieltjesNumerators_ne_parameters {c : ℝ} (hc : 0 < c) :
    ¬ ∃ u v : ℕ → ℝ, (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧
      pointStieltjesNumerators c = shiftedStieltjesNumerators c u v := by
  rintro ⟨u, v, hu, hv, heq⟩
  have h := le_shiftedStieltjesNumerators_even hc.le hu hv 1
  rw [← heq] at h
  have hzero : c ≤ 0 := by simpa only [pointStieltjesNumerators, ite_false,
      show (2 * 1 : ℕ) ≠ 0 by decide] using h
  exact (not_le_of_gt hc) hzero

end PowerSeries
