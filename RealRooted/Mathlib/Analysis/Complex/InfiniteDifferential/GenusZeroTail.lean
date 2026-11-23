/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.SmallTypeLimit
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Genus-zero canonical tails act like the identity

Summable real slopes may have either sign, may repeat, and may vanish.
The tail index is `k+n`, so the `n`th tail removes exactly the first `n` factors.
The target is any entire function of finite order.
-/

public section

open Filter Topology

namespace Complex

/-- Canonical genus-zero tail operators converge locally uniformly to the
identity on every finite-order entire target. Finite and empty products are
included by allowing zero slopes. This extends the scope of Cardon--de Gaston
(2005), Lemma 9, from LP targets to arbitrary finite-order entire targets. -/
theorem tendstoLocallyUniformly_infiniteDifferentialApply_linear_tail
    {a : ℕ → ℝ} (ha : Summable a) {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f ρ) :
    TendstoLocallyUniformly
      (fun n => infiniteDifferentialApply
        (fun z => ∏' k : ℕ, (1 + (a (k + n) : ℂ) * z)) f) f atTop := by
  let B : ℕ → ℝ := fun n => (∑' k : ℕ, ‖a (k + n)‖) + ((n : ℝ) + 1)⁻¹
  have hB (n : ℕ) : 0 < B n := by
    exact add_pos_of_nonneg_of_pos (tsum_nonneg fun _ => norm_nonneg _) (by positivity)
  have hlim : Tendsto B atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa only [B, add_zero] using (tendsto_sum_nat_add (fun k => ‖a k‖)).add hinv
  apply tendstoLocallyUniformly_infiniteDifferentialApply_of_type_tendsto_zero
    (B := B) _ _ hB hlim _ hf hof
  · intro n
    exact differentiable_tprod_one_add_ofReal_mul ((summable_nat_add_iff n).mpr ha)
  · intro n
    simp
  · intro n z
    have hs : Summable (fun k : ℕ => ‖(a (k + n) : ℂ) * z‖) := by
      simpa only [norm_mul, norm_real] using
        (((summable_nat_add_iff n).mpr ha).norm.mul_right ‖z‖)
    calc
      _ ≤ Real.exp (∑' k : ℕ, ‖(a (k + n) : ℂ) * z‖) :=
        TauCeti.norm_tprod_one_add_le_exp_tsum hs
      _ = Real.exp ((∑' k : ℕ, ‖a (k + n)‖) * ‖z‖) := by
        simp only [norm_mul, norm_real, tsum_mul_right]
      _ ≤ Real.exp (B n * ‖z‖) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp only [B]
        exact le_add_of_nonneg_right (by positivity)

end Complex
