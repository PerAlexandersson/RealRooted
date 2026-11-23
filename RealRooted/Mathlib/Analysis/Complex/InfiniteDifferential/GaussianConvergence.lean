/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianUniformBound
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Derivative
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Sharp Gaussian convergence for infinite differential operators

For global bounds `M exp(a norm(z)^2)` and `N exp(b norm(z)^2)`, the actual
differential series converges absolutely and locally uniformly if `4*a*b<1`.
Both Gaussian coefficients are positive here; minimal-type boundary cases
can be supplied by arbitrarily small positive bounds.
-/

public section

open Filter Topology

namespace Complex

/-- The sharp Gaussian condition supplies a summable scalar bound for the
differential terms on each spatial disk. -/
theorem exists_summable_differential_bound_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) (R : ℝ) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ n z, ‖z‖ ≤ R →
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤ B n := by
  obtain ⟨E, hE, B, hB0, hs, hB⟩ := exists_gaussian_differential_majorant
    hf hMφ hMf ha hb hab hfbound
  refine ⟨fun n ↦ B n * Real.exp (E * R ^ 2),
    hs.mul_right _, fun n z hz ↦ (hB φ hφ hφbound n z).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (hB0 n)
  apply Real.exp_le_exp.mpr
  gcongr

/-- Under the strict Gaussian threshold, the actual differential series is
absolutely convergent at every complex point. -/
theorem summable_norm_infiniteDifferentialApply_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖) := by
  obtain ⟨B, hs, hB⟩ := exists_summable_differential_bound_of_gaussian
    hφ hf hMφ hMf ha hb hab hφbound hfbound ‖z‖
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => hB n z le_rfl) hs

/-- Under the strict Gaussian threshold, the differential partial sums
converge uniformly on every disk. -/
theorem tendstoUniformlyOn_infiniteDifferentialApply_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) (R : ℝ) :
    TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))
      (infiniteDifferentialApply φ f) atTop {z | ‖z‖ ≤ R} := by
  obtain ⟨B, hs, hB⟩ := exists_summable_differential_bound_of_gaussian
    hφ hf hMφ hMf ha hb hab hφbound hfbound R
  exact tendstoUniformlyOn_tsum_nat hs hB

/-- The sharp Gaussian condition gives locally uniform convergence of the
actual differential series on the entire complex plane. -/
theorem tendstoLocallyUniformly_infiniteDifferentialApply_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N,
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))
      (infiniteDifferentialApply φ f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  exact (tendstoUniformlyOn_infiniteDifferentialApply_of_gaussian
    hφ hf hMφ hMf ha hb hab hφbound hfbound R).mono hR

/-- The actual differential image is entire under the strict Gaussian
threshold, without any reality hypothesis on the inputs. -/
theorem differentiable_infiniteDifferentialApply_of_gaussian {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hf : Differentiable ℂ f)
    {Mφ Mf a b : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    Differentiable ℂ (infiniteDifferentialApply φ f) := by
  apply differentiableOn_univ.mp
  apply (tendstoLocallyUniformlyOn_univ.mpr
    (tendstoLocallyUniformly_infiniteDifferentialApply_of_gaussian
      hφ hf hMφ hMf ha hb hab hφbound hfbound)).differentiableOn
        (Eventually.of_forall fun N =>
          (differentiable_partial_infiniteDifferentialApply hf N).differentiableOn) isOpen_univ

end Complex
