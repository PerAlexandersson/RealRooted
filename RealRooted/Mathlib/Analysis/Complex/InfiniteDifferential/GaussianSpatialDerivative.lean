/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianConvergence
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianJets
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Spatial derivatives commute with Gaussian differential operators
-/

public section

open Filter Topology

namespace Complex

/-- Under the strict Gaussian threshold, every spatial derivative commutes
with the actual infinite differential action. -/
theorem iteratedDeriv_infiniteDifferentialApply_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) (k : ℕ) :
    iteratedDeriv k (infiniteDifferentialApply φ f) =
      infiniteDifferentialApply φ (iteratedDeriv k f) := by
  have hbU : b < 1 / (4 * a) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  obtain ⟨d, hbd, hdU⟩ := exists_between hbU
  have hd : 0 < d := hb.trans hbd
  have had : 4 * a * d < 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * a)).mp hdU
    nlinarith
  let N : ℝ := k.factorial * Mf * Real.exp (b + b ^ 2 / (d - b))
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hdf := (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv k
    (WithTop.coe_lt_top _)
  have hleft := (tendstoLocallyUniformly_infiniteDifferentialApply_of_gaussian
    hφ hf hMφ hMf ha hb hab hφbound hfbound).iteratedDeriv
      (differentiable_partial_infiniteDifferentialApply hf) k
  simp only [iteratedDeriv_partial_infiniteDifferentialApply hf] at hleft
  have hright := tendstoLocallyUniformly_infiniteDifferentialApply_of_gaussian
    hφ hdf hMφ hN ha hd had hφbound
    (norm_iteratedDeriv_le_exp_sq hf hMf hb.le hbd hfbound k)
  ext z
  exact tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_univ.mpr hleft).tendsto_at (Set.mem_univ z))
    ((tendstoLocallyUniformlyOn_univ.mpr hright).tendsto_at (Set.mem_univ z))

end Complex
