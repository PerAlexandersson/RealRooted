/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Subquadratic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial factors retain arbitrarily close Gaussian bounds
-/

public section

open Polynomial

namespace Complex

/-- Multiplying by a polynomial retains any strictly larger quadratic
coefficient. Neither analyticity nor nonvanishing of the input is needed. -/
theorem exists_norm_polynomial_mul_le_exp_sq (P : ℂ[X]) {φ : ℂ → ℂ}
    {M a d : ℝ} (hM : 0 ≤ M) (had : a < d)
    (hbound : ∀ z, ‖φ z‖ ≤ M * Real.exp (a * ‖z‖ ^ 2)) :
    ∃ C > 0, ∀ z,
      ‖P.eval z * φ z‖ ≤ C * Real.exp (d * ‖z‖ ^ 2) := by
  obtain ⟨A, hA, hAbound⟩ := P.orderLE_eval.exists_norm_le_mul_exp_sq
    P.continuous (by norm_num) (sub_pos.mpr had)
  refine ⟨A * (M + 1), by positivity, fun z ↦ ?_⟩
  calc
    _ = ‖P.eval z‖ * ‖φ z‖ := norm_mul _ _
    _ ≤ (A * Real.exp ((d - a) * ‖z‖ ^ 2)) * (M * Real.exp (a * ‖z‖ ^ 2)) := by
      gcongr
      · exact hAbound z
      · exact hbound z
    _ = A * M * Real.exp (d * ‖z‖ ^ 2) := by
      rw [show d * ‖z‖ ^ 2 = (d - a) * ‖z‖ ^ 2 + a * ‖z‖ ^ 2 by ring,
        Real.exp_add]
      ring
    _ ≤ _ := by gcongr; exact le_add_of_nonneg_right zero_le_one

end Complex
