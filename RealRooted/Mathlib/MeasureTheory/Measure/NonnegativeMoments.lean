/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.MeasureTheory.Measure.MomentDeterminacy
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Moment

/-!
# Recovering nonnegative support by moment determinacy

A bounded real measure with genuine moments given by nonnegative Stieltjes
data equals the positive-half-line representing measure. The boundedness
hypothesis is what allows this conclusion about the supplied measure.
-/

public section

namespace MeasureTheory

/-- A bounded measure whose actual moment series has nonnegative Stieltjes
data is itself carried by the nonnegative half-line. -/
theorem ae_nonneg_of_bounded_stieltjes_moments {mu : Measure ℝ}
    {a : ℕ → ℝ} {mass R : ℝ} (ha : ∀ n, 0 ≤ a n) (hmass : 0 ≤ mass)
    (hbound : ∀ᵐ x ∂mu, |x| ≤ R)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu)
    (hf : PowerSeries.mk (fun n => ∫ x : ℝ, x ^ n ∂mu) =
      PowerSeries.C mass * PowerSeries.stieltjesTail a 0) :
    ∀ᵐ x ∂mu, 0 ≤ x := by
  let : IsFiniteMeasure mu :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using hint 0)
  obtain ⟨nu, _, hnu, hnuMom⟩ := PowerSeries.exists_measure_moments_of_eq_stieltjesTail ha hmass hf
  have heq : mu = nu := Measure.ext_of_integral_pow_eq_of_ae_bounded hbound
    (fun n => (hnuMom n).1) (fun n => by
      simpa only [PowerSeries.coeff_mk] using (hnuMom n).2.symm)
  simpa only [heq] using hnu

end MeasureTheory
