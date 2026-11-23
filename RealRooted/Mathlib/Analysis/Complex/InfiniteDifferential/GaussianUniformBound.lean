/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianBound
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianDerivative

/-!
# A common Gaussian majorant for families of differential symbols

The spatial Gaussian factor is separated from a summable sequence. The same
majorant works for every entire symbol satisfying the fixed norm bound.
-/

public section

namespace Complex

/-- The strict Gaussian threshold gives a common summable differential
majorant for all symbols satisfying the same global Gaussian bound. -/
theorem exists_gaussian_differential_majorant {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {Mφ Mf a b : ℝ}
    (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (ha : 0 < a) (hb : 0 < b)
    (hab : 4 * a * b < 1)
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (b * ‖w‖ ^ 2)) :
    ∃ E > 0, ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ Summable B ∧
      ∀ φ : ℂ → ℂ, Differentiable ℂ φ →
        (∀ w, ‖φ w‖ ≤ Mφ * Real.exp (a * ‖w‖ ^ 2)) → ∀ n z,
        ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ ≤
          B n * Real.exp (E * ‖z‖ ^ 2) := by
  have hbU : b < 1 / (4 * a) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  obtain ⟨d, hbd, hdU⟩ := exists_between hbU
  have hd : 0 < d := hb.trans hbd
  have had : 4 * a * d < 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * a)).mp hdU
    nlinarith
  let E : ℝ := b + b ^ 2 / (d - b)
  let q : ℝ := 2 * Real.sqrt (a * d)
  let C : ℝ := 2 * Real.exp 2 * Mφ * Mf
  have hE : 0 < E := by dsimp only [E]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq : q < 1 := by
    have hs := Real.sq_sqrt (mul_nonneg ha.le hd.le)
    dsimp only [q]
    nlinarith [Real.sqrt_nonneg (a * d)]
  have hqnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq
  have hg : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_lt_one hq0 hq
  have hng : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm
  have hsum : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * q ^ n) := by
    simpa only [add_mul, one_mul] using hng.add hg
  refine ⟨E, hE, fun n ↦ C * (((n : ℝ) + 1) * q ^ n),
    fun n ↦ by positivity, hsum.mul_left C, ?_⟩
  intro φ hφ hφbound n z
  have hcenter := norm_le_gaussian_center hMf hb.le hbd hfbound z
  have hterm := norm_differential_term_le_of_gaussian_center hφ hf hMφ
    (mul_nonneg hMf (Real.exp_pos _).le) ha hd hφbound z hcenter n
  calc
    _ ≤ (2 * Real.exp 2 * Mφ * (Mf * Real.exp (E * ‖z‖ ^ 2))) *
        ((n : ℝ) + 1) * q ^ n := hterm
    _ = _ := by dsimp only [C]; ring

end Complex
