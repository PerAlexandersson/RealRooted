/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderBound
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderConvergence
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Constant
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.OfBound
import RealRooted.Mathlib.Analysis.SpecificLimits.PowerSequence

/-!
# Growth bounds for entire differential images

The reciprocal-order estimate keeps its exponential dependence on the spatial
point. Summing its scalar majorant therefore controls the growth of the entire
differential image.
-/

public section

open Filter Topology

namespace Complex

/-- The differential image has a global exponential bound at any admissible
positive target growth exponent. -/
theorem exists_norm_infiniteDifferentialApply_le_exp_rpow {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    ∃ C > 0, ∀ z, ‖infiniteDifferentialApply φ f z‖ ≤ C * Real.exp (‖z‖ ^ q) := by
  obtain ⟨C, hC, hbound⟩ := exists_infiniteDifferentialApply_term_bound_of_order
    hφ hoφ hp hρ hf hof hq hσ
  let u : ℕ → ℝ := fun n => (Real.exp 2 / ((n : ℝ) + 1) ^ (p⁻¹ + q⁻¹ - 1)) ^ n
  have hu : Summable u := Real.summable_const_div_rpow_pow (by linarith) _
  have hun : 0 ≤ ∑' n, u n := tsum_nonneg fun n => by dsimp [u]; positivity
  refine ⟨C * ((∑' n, u n) + 1), by positivity, fun z => ?_⟩
  have hs := summable_norm_infiniteDifferentialApply_of_order
    hφ hoφ hp hρ hf hof hq hσ hsum z
  calc
    _ ≤ ∑' n : ℕ,
        ‖iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, C * Real.exp (‖z‖ ^ q) * u n :=
      hs.tsum_le_tsum (fun n => hbound n z) (hu.mul_left _)
    _ = C * Real.exp (‖z‖ ^ q) * (∑' n, u n) := tsum_mul_left
    _ ≤ _ := by nlinarith [Real.exp_pos (‖z‖ ^ q)]

end Complex

namespace TauCeti

/-- Under the reciprocal growth condition, an infinite differential operator
does not increase the target's growth order. Negative orders are included:
their entire functions are constant. -/
theorem OrderLE.infiniteDifferentialApply {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hof : OrderLE f σ) (hf : Differentiable ℂ f)
    (hφ : Differentiable ℂ φ) (hoφ : OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hσ : σ < q) (hsum : 1 < p⁻¹ + q⁻¹) :
    OrderLE (Complex.infiniteDifferentialApply φ f) σ := by
  by_cases hσ0 : 0 ≤ σ
  · rw [orderLE_def]
    intro r hr
    let q' := (σ + min q r) / 2
    have hm : σ < min q r := lt_min hσ hr
    have hq' : 0 < q' := by dsimp [q']; linarith
    have hσ' : σ < q' := by dsimp [q']; linarith
    have hq'q : q' < q := by dsimp [q']; linarith [min_le_left q r]
    have hq'r : q' < r := by dsimp [q']; linarith [min_le_right q r]
    have hi : q⁻¹ ≤ q'⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hq' hq'q.le
    have hsum' : 1 < p⁻¹ + q'⁻¹ := hsum.trans_le (add_le_add le_rfl hi)
    obtain ⟨C, _, hbound⟩ := Complex.exists_norm_infiniteDifferentialApply_le_exp_rpow
      hφ hoφ hp hρ hf hof hq' hσ' hsum'
    have ho : OrderLE (Complex.infiniteDifferentialApply φ f) q' :=
      orderLE_of_norm_le_mul_exp_rpow (C := 1) (by simpa only [one_mul] using hbound)
    exact ho.isBigO hq'r
  · have hconst := hof.isConst hf (lt_of_not_ge hσ0)
    have heq : f = fun _ => f 0 := funext fun z => hconst z 0
    rw [heq, Complex.infiniteDifferentialApply_const]
    exact orderLE_const _ σ

end TauCeti
