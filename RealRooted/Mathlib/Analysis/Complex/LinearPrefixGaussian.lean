/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Common Gaussian envelopes for summable linear-product prefixes
-/

public section

namespace Complex

/-- Completing the square bounds a linear term by any positive quadratic term. -/
private theorem mul_le_sq_add_div {ε S r : ℝ} (hε : 0 < ε) :
    S * r ≤ ε * r ^ 2 + S ^ 2 / (4 * ε) := by
  have hsq := mul_nonneg hε.le (sq_nonneg (r - S / (2 * ε)))
  have heq : ε * (r - S / (2 * ε)) ^ 2 =
      ε * r ^ 2 - S * r + S ^ 2 / (4 * ε) := by
    field_simp [hε.ne']
    ring
  rw [heq] at hsq
  linarith

/-- Every finite prefix of a summable real linear product admits the same
global bound with any positive quadratic coefficient. -/
theorem exists_norm_prod_one_add_le_exp_sq {a : ℕ → ℝ} (ha : Summable a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ n z,
      ‖∏ j ∈ Finset.range n, (1 + (a j : ℂ) * z)‖ ≤ C * Real.exp (ε * ‖z‖ ^ 2) := by
  let S : ℝ := ∑' j, ‖a j‖
  refine ⟨Real.exp (S ^ 2 / (4 * ε)), Real.exp_pos _, fun n z ↦ ?_⟩
  have hprefix : ‖∏ j ∈ Finset.range n, (1 + (a j : ℂ) * z)‖ ≤
      Real.exp (‖z‖ * ∑ j ∈ Finset.range n, ‖a j‖) := by
    simpa only [Fin.prod_univ_eq_prod_range (fun j ↦ (1 + (a j : ℂ) * z)) n,
      norm_real, Fin.sum_univ_eq_sum_range (fun j ↦ ‖a j‖) n] using
      norm_prod_one_add_le_exp (fun j : Fin n ↦ (a j : ℂ)) z
  have hsum : (∑ j ∈ Finset.range n, ‖a j‖) ≤ S :=
    ha.norm.sum_le_tsum _ (fun j _ ↦ norm_nonneg _)
  calc
    _ ≤ Real.exp (‖z‖ * ∑ j ∈ Finset.range n, ‖a j‖) := hprefix
    _ ≤ Real.exp (‖z‖ * S) := by gcongr
    _ ≤ Real.exp (ε * ‖z‖ ^ 2 + S ^ 2 / (4 * ε)) :=
      Real.exp_le_exp.mpr (by simpa only [mul_comm] using
        (mul_le_sq_add_div (S := S) (r := ‖z‖) hε))
    _ = _ := by rw [Real.exp_add, mul_comm]

end Complex
