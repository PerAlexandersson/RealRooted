/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Exponential bounds from geometric Taylor derivative bounds

A geometric bound on the derivatives of an entire function sums to an
exponential bound on its norm. The codomain may be any complex Banach space.
-/

public section

/-- Geometrically bounded Taylor derivatives give an exponential norm bound
for an entire function with values in a complex Banach space. -/
theorem Differentiable.norm_le_mul_exp_of_iteratedDeriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} (hf : Differentiable ℂ f) {c : ℂ} {C A : ℝ}
    (hcoeff : ∀ n, ‖iteratedDeriv n f c‖ ≤ C * A ^ n) (z : ℂ) :
    ‖f z‖ ≤ C * Real.exp (A * ‖z - c‖) := by
  have hsum : HasSum (fun n : ℕ => C * ((A * ‖z - c‖) ^ n / n.factorial))
      (C * Real.exp (A * ‖z - c‖)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (A * ‖z - c‖)).mul_left C
  apply (Complex.hasSum_taylorSeries_of_entire hf c z).norm_le_of_bounded hsum
  intro n
  simp only [norm_smul, norm_inv, norm_natCast, norm_pow]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * (‖z - c‖ ^ n * (C * A ^ n)) := by
      gcongr
      exact hcoeff n
    _ = C * ((A * ‖z - c‖) ^ n / n.factorial) := by rw [mul_pow]; ring
