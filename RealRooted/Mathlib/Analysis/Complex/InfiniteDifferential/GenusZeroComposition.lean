/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianApproxComposition
import RealRooted.Mathlib.Analysis.Complex.LinearPrefixGaussian
import RealRooted.Mathlib.Analysis.Complex.LinearProduct

/-!
# Summable linear factors compose with Gaussian differential symbols
-/

public section

open Complex Filter Polynomial Topology

namespace Complex

/-- A summable real genus-zero factor composes with a Gaussian-convergent
symbol. This is an identity of the actual infinite differential images. -/
theorem infiniteDifferentialApply_linearProduct_mul {a : ℕ → ℝ} (ha : Summable a)
    {φ f : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf A B : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (hA : 0 < A) (hB : 0 < B)
    (hAB : 4 * A * B < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (A * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (B * ‖w‖ ^ 2)) :
    infiniteDifferentialApply (fun z ↦ (∏' j, (1 + (a j : ℂ) * z)) * φ z) f =
      infiniteDifferentialApply (fun z ↦ ∏' j, (1 + (a j : ℂ) * z))
        (infiniteDifferentialApply φ f) := by
  let P : ℕ → ℂ[X] := fun n ↦ ∏ j ∈ Finset.range n, (1 + C (a j : ℂ) * X)
  have heval (n : ℕ) (z : ℂ) :
      (P n).eval z = ∏ j ∈ Finset.range n, (1 + (a j : ℂ) * z) := by
    simp only [P, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X]
  have hP : TendstoLocallyUniformly (fun n z ↦ (P n).eval z)
      (fun z ↦ ∏' j, (1 + (a j : ℂ) * z)) atTop := by
    simpa only [heval] using tendstoLocallyUniformly_prod_one_add a ha
  apply infiniteDifferentialApply_mul_of_polynomial_approx hP _ hφ hf hMφ hMf hA hB hAB
    hφbound hfbound
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := exists_norm_prod_one_add_le_exp_sq ha hε
  exact ⟨C, hC, fun n z ↦ by simpa only [heval] using hbound n z⟩

end Complex
