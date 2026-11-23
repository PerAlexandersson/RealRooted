/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianUniformBound
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Continuity of Gaussian differential operators in the symbol

A common Gaussian envelope is essential. Locally uniform convergence of
symbols alone does not justify passing a limit through an infinite operator.
-/

public section

open Filter Topology

namespace Complex

/-- Locally uniform symbol convergence with a common Gaussian envelope
passes through the actual infinite differential action at every point. -/
theorem tendsto_infiniteDifferentialApply_of_gaussian {Φ : ℕ → ℂ → ℂ} {φ f : ℂ → ℂ}
    (hΦ : ∀ i, Differentiable ℂ (Φ i))
    (hlim : TendstoLocallyUniformly Φ φ atTop) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hΦbound : ∀ i w, ‖Φ i w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) (z : ℂ) :
    Tendsto (fun i ↦ infiniteDifferentialApply (Φ i) f z) atTop
      (𝓝 (infiniteDifferentialApply φ f z)) := by
  obtain ⟨E, _, B, _, hs, hB⟩ := exists_gaussian_differential_majorant
    hf hMφ hMf ha hb hab hfbound
  have hd (n : ℕ) : Tendsto (fun i ↦ iteratedDeriv n (Φ i) 0) atTop
      (𝓝 (iteratedDeriv n φ 0)) :=
    (tendstoLocallyUniformlyOn_univ.mpr (hlim.iteratedDeriv hΦ n)).tendsto_at
      (Set.mem_univ 0)
  have hterm (n : ℕ) : Tendsto
      (fun i ↦ iteratedDeriv n (Φ i) 0 * iteratedDeriv n f z / (n.factorial : ℂ)) atTop
      (𝓝 (iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))) :=
    ((hd n).mul_const _).div_const _
  exact tendsto_tsum_of_dominated_convergence
    (hs.mul_right (Real.exp (E * ‖z‖ ^ 2))) hterm
    (Eventually.of_forall fun i n ↦ hB (Φ i) (hΦ i) (hΦbound i) n z)

end Complex
