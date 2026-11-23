/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis

/-!
# Global logarithmic growth on the positive left contour line

The large-height estimate combines with continuity on a compact interval to
give a logarithmic bound at every height. This retains the logarithmic growth
needed to bound finite differences of the remaining Perron integral.
-/

public section

open Complex Set

namespace RiemannHypothesis

/-- Under RH, a global logarithmic bound holds on the positive line `Re s = 9 / 20`. -/
theorem exists_norm_logDeriv_riemannZeta_le_log_add_abs (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((9 / 20 : ℂ) + I * t)‖ ≤ C * Real.log (2 + |t|) := by
  have hcont : Continuous (fun t : ℝ ↦ logDeriv riemannZeta ((9 / 20 : ℂ) + I * t)) := by
    simpa using hRH.continuous_logDeriv_riemannZeta_line
      (σ := 9 / 20) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨B, hB, htail⟩ := hRH.exists_norm_logDeriv_riemannZeta_le_log
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B + |D| / Real.log 2 + 1, by positivity, fun t ↦ ?_⟩
  have hlow : Real.log 2 ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog : 0 ≤ Real.log (2 + |t|) := hlog2.le.trans hlow
  by_cases ht : 3 ≤ |t|
  · have hcomp : Real.log |t| ≤ Real.log (2 + |t|) :=
      Real.log_le_log (by linarith) (by linarith)
    calc
      _ ≤ B * Real.log |t| := htail t ht
      _ ≤ B * Real.log (2 + |t|) := mul_le_mul_of_nonneg_left hcomp hB.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by
          have : 0 ≤ |D| / Real.log 2 := by positivity
          linarith) hlog
  · have hmem : t ∈ Icc (-3 : ℝ) 3 := by
      have habs := abs_le.mp (le_of_lt (lt_of_not_ge ht))
      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    calc
      _ ≤ D := hD t hmem
      _ ≤ |D| := le_abs_self D
      _ = (|D| / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ (|D| / Real.log 2) * Real.log (2 + |t|) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlog

end RiemannHypothesis
