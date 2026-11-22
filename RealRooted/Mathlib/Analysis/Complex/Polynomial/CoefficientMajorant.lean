/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic

/-!
# Nonnegative coefficient majorants on complex disks
-/

public section

open Complex

namespace Polynomial

/-- A real polynomial with nonnegative coefficients is a radial majorant for
its own complexification on every closed disk. -/
theorem norm_eval_map_le_of_coeff_nonneg {p : ℝ[X]} (hp : ∀ k, 0 ≤ p.coeff k)
    {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖(p.map ofRealHom).eval z‖ ≤ p.eval R := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Polynomial.sum_def]
  calc
    _ ≤ ∑ k ∈ p.support, ‖ofRealHom (p.coeff k) * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ p.support, p.coeff k * R ^ k := by
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul, ofRealHom_eq_coe, norm_real, Real.norm_of_nonneg (hp k), norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg z) hz k) (hp k)

end Polynomial
