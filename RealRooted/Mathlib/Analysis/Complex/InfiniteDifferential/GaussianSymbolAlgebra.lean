/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.SymbolSummable
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianConvergence
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianSpatialDerivative
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianJets

/-!
# Algebra of Gaussian infinite differential symbols
-/

public section

namespace Complex

/-- Gaussian-convergent differential images are linear in the symbol. -/
theorem infiniteDifferentialApply_add_symbol_of_gaussian {φ ψ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hψ : Differentiable ℂ ψ) (hf : Differentiable ℂ f)
    {Mφ Mψ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMψ : 0 ≤ Mψ) (hMf : 0 ≤ Mf)
    (ha : 0 < a) (hb : 0 < b) (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hψbound : ∀ w, ‖ψ w‖ ≤ Mψ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    infiniteDifferentialApply (fun z ↦ φ z + ψ z) f =
      infiniteDifferentialApply φ f + infiniteDifferentialApply ψ f := by
  exact infiniteDifferentialApply_add_symbol_of_summable hφ hψ
    (fun z ↦ (summable_norm_infiniteDifferentialApply_of_gaussian
      hφ hf hMφ hMf ha hb hab hφbound hfbound z).of_norm)
    (fun z ↦ (summable_norm_infiniteDifferentialApply_of_gaussian
      hψ hf hMψ hMf ha hb hab hψbound hfbound z).of_norm)

/-- A variable factor differentiates the target in the Gaussian range. -/
theorem infiniteDifferentialApply_id_mul_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    infiniteDifferentialApply (fun z ↦ z * φ z) f =
      infiniteDifferentialApply φ (deriv f) := by
  have hbU : b < 1 / (4 * a) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  obtain ⟨d, hbd, hdU⟩ := exists_between hbU
  have hd : 0 < d := hb.trans hbd
  have had : 4 * a * d < 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * a)).mp hdU
    nlinarith
  let N : ℝ := Mf * Real.exp (b + b ^ 2 / (d - b))
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hdfbound (w : ℂ) : ‖deriv f w‖ ≤ N * Real.exp (d * ‖w‖ ^ 2) := by
    simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul] using
      norm_iteratedDeriv_le_exp_sq hf hMf hb.le hbd hfbound 1 w
  apply infiniteDifferentialApply_id_mul_of_summable hφ
  intro z
  exact (summable_norm_infiniteDifferentialApply_of_gaussian
    hφ hf.deriv hMφ hN ha hd had hφbound hdfbound z).of_norm

/-- A variable factor differentiates the actual Gaussian differential image. -/
theorem infiniteDifferentialApply_id_mul_eq_deriv_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    infiniteDifferentialApply (fun z ↦ z * φ z) f =
      deriv (infiniteDifferentialApply φ f) := by
  rw [infiniteDifferentialApply_id_mul_of_gaussian hφ hf hMφ hMf ha hb hab
    hφbound hfbound]
  simpa only [iteratedDeriv_one] using
    (iteratedDeriv_infiniteDifferentialApply_of_gaussian
      hφ hf hMφ hMf ha hb hab hφbound hfbound 1).symm

end Complex
