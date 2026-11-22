/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.IntervalIntegral.MonotoneBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Recovering a monotone function from its integrated error

Bounds on the differences of `∫₀ˣ f - x²/2` give bounds on the adjacent integral
means of `f`. Monotonicity then recovers a pointwise bound for `f(x) - x`.
-/

public section

open MeasureTheory

namespace Monotone

/-- Finite differences of the primitive error control the pointwise error of a monotone function. -/
theorem abs_sub_le_of_integral_sub_quadratic_bounds {f : ℝ → ℝ} (hf : Monotone f)
    {x h ε : ℝ} (hh : 0 < h)
    (hback : |(((∫ t in (0 : ℝ)..x, f t) - x ^ 2 / 2) -
      ((∫ t in (0 : ℝ)..x - h, f t) - (x - h) ^ 2 / 2)) / h| ≤ ε)
    (hforward : |(((∫ t in (0 : ℝ)..x + h, f t) - (x + h) ^ 2 / 2) -
      ((∫ t in (0 : ℝ)..x, f t) - x ^ 2 / 2)) / h| ≤ ε) :
    |f x - x| ≤ h / 2 + ε := by
  apply hf.abs_sub_le_of_integral_bounds hh
  · calc
      |(∫ t in x - h..x, f t) / h - (x - h / 2)| =
          |(((∫ t in (0 : ℝ)..x, f t) - x ^ 2 / 2) -
            ((∫ t in (0 : ℝ)..x - h, f t) - (x - h) ^ 2 / 2)) / h| := by
        congr 1
        rw [← intervalIntegral.integral_interval_sub_left (a := 0)
          hf.intervalIntegrable hf.intervalIntegrable]
        field_simp [hh.ne']
        ring
      _ ≤ ε := hback
  · calc
      |(∫ t in x..x + h, f t) / h - (x + h / 2)| =
          |(((∫ t in (0 : ℝ)..x + h, f t) - (x + h) ^ 2 / 2) -
            ((∫ t in (0 : ℝ)..x, f t) - x ^ 2 / 2)) / h| := by
        congr 1
        rw [← intervalIntegral.integral_interval_sub_left (a := 0)
          hf.intervalIntegrable hf.intervalIntegrable]
        field_simp [hh.ne']
        ring
      _ ≤ ε := hforward

end Monotone
