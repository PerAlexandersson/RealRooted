/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.FourierSummand
import RealRooted.Mathlib.Analysis.Polynomial.GaussianMajorant

/-!
# Locally uniform summable bounds for the xi Fourier summands

Every derivative order has a common summable majorant on each compact real
interval. Both positive and negative values of the real parameter are covered.
-/

public section

open Real Set

/-- Each derivative family of Fourier summands has a summable bound on a real interval. -/
theorem exists_summable_bound_riemannXiFourierTerm (j : ℕ) (a b : ℝ) :
    ∃ M : ℕ → ℝ, Summable M ∧
      ∀ n t, t ∈ Icc a b → ‖riemannXiFourierTerm j n t‖ ≤ M n := by
  obtain ⟨M, hM, hbound⟩ :=
    (riemannXiFourierPolynomial j).exists_summable_bound_nat_pow_eval_exp 2
      (mul_pos pi_pos (exp_pos (4 * a))) (π * exp (4 * b)) (5 * b)
  refine ⟨fun n => π * M n, hM.mul_left π, ?_⟩
  intro n t ht
  have h := hbound n (π * exp (4 * t)) (5 * t)
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [ht.1])) pi_pos.le)
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [ht.2])) pi_pos.le)
    (by linarith [ht.2])
  have harg : π * (n : ℝ) ^ 2 * exp (4 * t) = (π * exp (4 * t)) * n ^ 2 := by ring
  have heq : riemannXiFourierTerm j n t = π *
      ((n : ℝ) ^ 2 * (riemannXiFourierPolynomial j).eval ((π * exp (4 * t)) * n ^ 2) *
        exp (5 * t - (π * exp (4 * t)) * n ^ 2)) := by
    rw [riemannXiFourierTerm, harg]
    ring
  rw [heq, norm_mul, norm_of_nonneg pi_pos.le]
  exact mul_le_mul_of_nonneg_left h pi_pos.le

/-- Every derivative series of the Fourier kernel converges absolutely at each real point. -/
theorem summable_norm_riemannXiFourierTerm (j : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => ‖riemannXiFourierTerm j n t‖) := by
  obtain ⟨M, hM, hbound⟩ := exists_summable_bound_riemannXiFourierTerm j t t
  exact hM.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => hbound n t ⟨le_rfl, le_rfl⟩)

/-- Every derivative series of the Fourier kernel is genuinely summable. -/
theorem summable_riemannXiFourierTerm (j : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => riemannXiFourierTerm j n t) :=
  (summable_norm_riemannXiFourierTerm j t).of_norm
