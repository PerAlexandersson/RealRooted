/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Real beta integrals

This file extracts the real interval-integral form of the beta integral from
Mathlib's complex-valued API.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace intervalIntegral

private theorem betaWeight_eq_re_betaIntegrand
    {a b x : ℝ} (hx : x ∈ Set.uIoo (0 : ℝ) 1) :
    x ^ a * (1 - x) ^ b =
      ((x : ℂ) ^ (((a + 1 : ℝ) : ℂ) - 1) *
        (1 - (x : ℂ)) ^ (((b + 1 : ℝ) : ℂ) - 1)).re := by
  have hxpos : 0 < x := by simpa using hx.1
  have hxone : 0 < 1 - x := by simpa using hx.2
  norm_cast
  rw [← Complex.ofReal_cpow hxpos.le, ← Complex.ofReal_cpow hxone.le]
  norm_num

/-- The real beta weight is interval integrable in its classical parameter
range. -/
theorem intervalIntegrable_rpow_mul_one_sub_rpow
    {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ a * (1 - x) ^ b)
      volume 0 1 := by
  have hcomplex := Complex.betaIntegral_convergent
    (u := ((a + 1 : ℝ) : ℂ)) (v := ((b + 1 : ℝ) : ℂ))
    (by norm_num; linarith) (by norm_num; linarith)
  have hre : IntervalIntegrable
      (fun x : ℝ =>
        ((x : ℂ) ^ (((a + 1 : ℝ) : ℂ) - 1) *
          (1 - (x : ℂ)) ^ (((b + 1 : ℝ) : ℂ) - 1)).re)
      volume 0 1 :=
    ⟨hcomplex.1.re, hcomplex.2.re⟩
  exact hre.congr_uIoo fun x hx => (betaWeight_eq_re_betaIntegrand hx).symm

/-- The classical real beta integral in Gamma-function form. -/
theorem integral_rpow_mul_one_sub_rpow_zero_one
    {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    (∫ x : ℝ in 0..1, x ^ a * (1 - x) ^ b) =
      Real.Gamma (a + 1) * Real.Gamma (b + 1) /
        Real.Gamma (a + b + 2) := by
  have hcomplex := Complex.betaIntegral_convergent
    (u := ((a + 1 : ℝ) : ℂ)) (v := ((b + 1 : ℝ) : ℂ))
    (by norm_num; linarith) (by norm_num; linarith)
  calc
    (∫ x : ℝ in 0..1, x ^ a * (1 - x) ^ b) =
        ∫ x : ℝ in 0..1,
          ((x : ℂ) ^ (((a + 1 : ℝ) : ℂ) - 1) *
            (1 - (x : ℂ)) ^ (((b + 1 : ℝ) : ℂ) - 1)).re := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      exact betaWeight_eq_re_betaIntegrand hx
    _ = (Complex.betaIntegral (a + 1) (b + 1)).re := by
      rw [Complex.betaIntegral]
      convert intervalIntegral_re hcomplex using 1 <;> norm_num
    _ = Real.Gamma (a + 1) * Real.Gamma (b + 1) /
        Real.Gamma (a + b + 2) := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _
        (by norm_num; linarith) (by norm_num; linarith)]
      rw [show (a : ℂ) + 1 = ((a + 1 : ℝ) : ℂ) by norm_num,
        show (b : ℂ) + 1 = ((b + 1 : ℝ) : ℂ) by norm_num,
        show ((a + 1 : ℝ) : ℂ) + (b + 1 : ℝ) =
          ((a + b + 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.Gamma_ofReal, Complex.Gamma_ofReal,
        Complex.Gamma_ofReal]
      norm_cast

end intervalIntegral
