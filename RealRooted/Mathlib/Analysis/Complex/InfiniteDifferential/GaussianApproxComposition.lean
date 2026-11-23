/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianSymbolLimit
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianImageGrowth
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianConvergence
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianPolynomialComposition
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.PolynomialSymbol
import RealRooted.Mathlib.Topology.Algebra.IsUniformGroup.FiniteSum
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Infinite factor composition from controlled polynomial approximation

An extra symbol whose polynomial approximants admit common arbitrarily small
Gaussian bounds can be passed through a Gaussian-convergent operator. Both
limits are the actual derivative-normalized differential series.
-/

public section

open Filter Polynomial Topology

namespace Complex

/-- A small symbol coefficient preserves both strict Gaussian thresholds. -/
private theorem exists_gaussian_composition_margin {a b E : ℝ}
    (hb : 0 < b) (hE : 0 < E) (hab : 4 * a * b < 1) :
    ∃ ε > 0, 4 * (a + ε) * b < 1 ∧ 4 * ε * E < 1 := by
  have haU : a < 1 / (4 * b) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hU : 0 < 1 / (4 * b) - a := sub_pos.mpr haU
  have hV : 0 < 1 / (4 * E) := by positivity
  obtain ⟨ε, hε, hεUV⟩ := exists_between (lt_min hU hV)
  have hεU := hεUV.trans_le (min_le_left _ _)
  have hεV := hεUV.trans_le (min_le_right _ _)
  refine ⟨ε, hε, ?_, ?_⟩
  · have h := (lt_div_iff₀ (by positivity : 0 < 4 * b)).mp
      (show a + ε < 1 / (4 * b) by linarith)
    nlinarith
  · have h := (lt_div_iff₀ (by positivity : 0 < 4 * E)).mp hεV
    nlinarith

/-- A symbol with uniformly minimal-Gaussian polynomial approximants
composes with a Gaussian differential operator. The conclusion includes zero
outputs and supplies the genuine infinite-factor composition identity. -/
theorem infiniteDifferentialApply_mul_of_polynomial_approx
    {P : ℕ → ℂ[X]} {ψ φ f : ℂ → ℂ}
    (hP : TendstoLocallyUniformly (fun n z ↦ (P n).eval z) ψ atTop)
    (hPbound : ∀ ε > 0, ∃ C > 0, ∀ n z, ‖(P n).eval z‖ ≤ C * Real.exp (ε * ‖z‖ ^ 2))
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    infiniteDifferentialApply (fun z ↦ ψ z * φ z) f =
      infiniteDifferentialApply ψ (infiniteDifferentialApply φ f) := by
  let g := infiniteDifferentialApply φ f
  have hg : Differentiable ℂ g := differentiable_infiniteDifferentialApply_of_gaussian
    hφ hf hMφ hMf ha hb hab hφbound hfbound
  obtain ⟨M, hM, E, hE, hgBound⟩ := exists_norm_infiniteDifferentialApply_le_exp_sq
    hφ hf hMφ hMf ha hb hab hφbound hfbound
  obtain ⟨ε, hε, hsum, hεE⟩ := exists_gaussian_composition_margin hb hE hab
  obtain ⟨C, hC, hCbound⟩ := hPbound ε hε
  have hprodlim : TendstoLocallyUniformly
      (fun n z ↦ (P n).eval z * φ z) (fun z ↦ ψ z * φ z) atTop := by
    simpa only [Pi.mul_def] using hP.mul₀ (tendstoLocallyUniformly_const_family φ atTop)
      (hP.continuous (Frequently.of_forall fun n ↦ (P n).continuous)) hφ.continuous
  have hprodBound (n : ℕ) (z : ℂ) :
      ‖(P n).eval z * φ z‖ ≤ (C * Mφ) * Real.exp ((a + ε) * ‖z‖ ^ 2) := by
    calc
      _ = ‖(P n).eval z‖ * ‖φ z‖ := norm_mul _ _
      _ ≤ (C * Real.exp (ε * ‖z‖ ^ 2)) * (Mφ * Real.exp (a * ‖z‖ ^ 2)) := by
        gcongr
        · exact hCbound n z
        · exact hφbound z
      _ = _ := by rw [add_mul, Real.exp_add]; ring
  ext z
  have hleft := tendsto_infiniteDifferentialApply_of_gaussian
    (fun n ↦ by fun_prop) hprodlim hf (mul_nonneg hC.le hMφ) hMf
      (add_pos ha hε) hb hsum hprodBound hfbound z
  have hright := tendsto_infiniteDifferentialApply_of_gaussian
    (fun n ↦ (P n).differentiable) hP hg hC.le hM.le hε hE hεE hCbound hgBound z
  have heq (n : ℕ) :
      infiniteDifferentialApply (fun w ↦ (P n).eval w * φ w) f z =
        infiniteDifferentialApply (fun w ↦ (P n).eval w) g z := by
    rw [infiniteDifferentialApply_polynomial_mul_of_gaussian (P n)
      hφ hf hMφ hMf ha hb hab hφbound hfbound, infiniteDifferentialApply_polynomial]
  exact tendsto_nhds_unique (hleft.congr' (Eventually.of_forall heq)) hright

end Complex
