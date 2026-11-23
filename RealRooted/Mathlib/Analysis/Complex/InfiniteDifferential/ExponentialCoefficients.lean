/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville

/-!
# Taylor bounds for entire functions of small exponential type

Cauchy's circle is centered at zero, with radius `(n+1)/B`. The bound therefore
retains the small exponential type `B` in every positive Taylor coefficient.
-/

public section

open Metric

namespace Complex

/-- An exponential norm bound controls every derivative at the origin, retaining
the exponential type. The prefactor also handles derivative order zero. -/
theorem norm_iteratedDeriv_zero_le_of_exp_norm_bound {φ : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z, ‖φ z‖ ≤ Real.exp (B * ‖z‖)) (n : ℕ) :
    ‖iteratedDeriv n φ 0‖ ≤
      n.factorial * Real.exp 1 * (Real.exp 1 * B / ((n : ℝ) + 1)) ^ n := by
  let r : ℝ := ((n : ℝ) + 1) / B
  have hr : 0 < r := div_pos (by positivity) hB
  have hBr : B * r = (n : ℝ) + 1 := by dsimp [r]; field_simp [hB.ne']
  have hc : ∀ z ∈ sphere (0 : ℂ) r,
      ‖φ z‖ ≤ Real.exp ((n : ℝ) + 1) := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    simpa only [hz', hBr] using hbound z
  calc
    _ ≤ n.factorial * Real.exp ((n : ℝ) + 1) / r ^ n :=
      norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hφ.diffContOnCl hc
    _ = _ := by
      rw [Real.exp_add, ← Real.exp_one_pow]
      dsimp only [r]
      simp only [div_pow, mul_pow]
      field_simp [hB.ne']

end Complex
