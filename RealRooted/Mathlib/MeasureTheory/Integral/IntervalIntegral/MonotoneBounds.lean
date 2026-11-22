/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-!
# Recovering a monotone function from neighboring integral means

The backward integral mean is at most the value at the common endpoint, and
the forward mean is at least that value. Consequently bounds for the two
means around the means of the identity function give a pointwise error bound.
-/

public section

open MeasureTheory Set

namespace Monotone

/-- The backward mean of a monotone function is at most its endpoint value. -/
theorem integral_sub_div_le {f : ℝ → ℝ} (hf : Monotone f) {x h : ℝ} (hh : 0 < h) :
    (∫ t in x - h..x, f t) / h ≤ f x := by
  rw [div_le_iff₀ hh]
  have hbound := intervalIntegral.integral_mono_on (μ := volume)
    (by linarith : x - h ≤ x)
    hf.intervalIntegrable intervalIntegrable_const
    (fun t (ht : t ∈ Icc (x - h) x) ↦ hf ht.2)
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hbound

/-- The forward mean of a monotone function is at least its initial value. -/
theorem le_integral_add_div {f : ℝ → ℝ} (hf : Monotone f) {x h : ℝ} (hh : 0 < h) :
    f x ≤ (∫ t in x..x + h, f t) / h := by
  rw [le_div_iff₀ hh]
  have hbound := intervalIntegral.integral_mono_on (μ := volume)
    (by linarith : x ≤ x + h)
    intervalIntegrable_const hf.intervalIntegrable
    (fun t (ht : t ∈ Icc x (x + h)) ↦ hf ht.1)
  simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hbound

/-- Bounds for the adjacent means of a monotone function yield a pointwise bound
relative to the identity function, with the smoothing error `h / 2`. -/
theorem abs_sub_le_of_integral_bounds {f : ℝ → ℝ} (hf : Monotone f)
    {x h ε : ℝ} (hh : 0 < h)
    (hback : |(∫ t in x - h..x, f t) / h - (x - h / 2)| ≤ ε)
    (hforward : |(∫ t in x..x + h, f t) / h - (x + h / 2)| ≤ ε) :
    |f x - x| ≤ h / 2 + ε := by
  have hlo := hf.integral_sub_div_le (x := x) hh
  have hhi := hf.le_integral_add_div (x := x) hh
  obtain ⟨hb, _⟩ := abs_le.mp hback
  obtain ⟨_, hfwd⟩ := abs_le.mp hforward
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Monotone
