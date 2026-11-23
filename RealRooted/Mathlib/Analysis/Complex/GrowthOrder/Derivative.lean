/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder

/-!
# Growth order of derivatives

Every iterated derivative of an entire function has at most the same growth order.
Cauchy's estimate on a unit circle transfers an exponential power bound to the
derivative. A slight increase in the exponent absorbs the change of radius.
-/

public section

open Complex Filter Asymptotics Bornology Metric Topology

namespace TauCeti.OrderLE

/-- Iterated differentiation does not increase the growth order of an entire function. -/
theorem iteratedDeriv {f : ℂ → ℂ} {A : ℝ} (h : TauCeti.OrderLE f A)
    (hf : Differentiable ℂ f) (n : ℕ) : TauCeti.OrderLE (iteratedDeriv n f) A := by
  rcases lt_or_ge A 0 with hA | hA
  · have heq : f = fun _ => f 0 := funext fun z => h.isConst hf hA z 0
    rw [heq]
    convert TauCeti.orderLE_const (if n = 0 then f 0 else 0) A using 1
    funext z
    exact iteratedDeriv_const
  · rw [TauCeti.orderLE_def]
    intro B hB
    let q : ℝ := (A + B) / 2
    have hAq : A < q := by dsimp [q]; linarith
    have hqB : q < B := by dsimp [q]; linarith
    have hq : 0 ≤ q := hA.trans hAq.le
    obtain ⟨C, hC, hbound⟩ := (h.isBigO hAq).exists_pos
    obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hbound.bound
    refine (IsBigO.of_bound ((n.factorial : ℝ) * C) ?_).trans
      (TauCeti.isBigO_exp_mul_norm_rpow ((2 : ℝ) ^ q) hqB)
    filter_upwards [eventually_cobounded_le_norm (max 1 (R + 1))] with z hz
    have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
    have hzR : R + 1 ≤ ‖z‖ := (le_max_right _ _).trans hz
    have hcircle : ∀ w ∈ sphere z 1,
        ‖f w‖ ≤ C * Real.exp ((2 : ℝ) ^ q * ‖z‖ ^ q) := by
      intro w hw
      have hwz : ‖w - z‖ = 1 := mem_sphere_iff_norm.mp hw
      have hupper : ‖w‖ ≤ 2 * ‖z‖ := by
        have htri := norm_add_le (w - z) z
        rw [sub_add_cancel, hwz] at htri
        linarith
      have hlower : R ≤ ‖w‖ := by
        have htri := norm_add_le (z - w) w
        rw [sub_add_cancel, norm_sub_rev, hwz] at htri
        linarith
      calc
        ‖f w‖ ≤ C * Real.exp (‖w‖ ^ q) := by
          simpa only [Real.norm_eq_abs, Real.abs_exp] using hR hlower
        _ ≤ C * Real.exp ((2 : ℝ) ^ q * ‖z‖ ^ q) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply Real.exp_le_exp.mpr
          calc
            ‖w‖ ^ q ≤ (2 * ‖z‖) ^ q := Real.rpow_le_rpow (norm_nonneg _) hupper hq
            _ = (2 : ℝ) ^ q * ‖z‖ ^ q := Real.mul_rpow (by positivity) (norm_nonneg _)
    simpa only [Real.norm_eq_abs, Real.abs_exp, one_pow, div_one, mul_assoc] using
      norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n zero_lt_one hf.diffContOnCl hcircle

/-- Differentiation does not increase the growth order of an entire function. -/
theorem deriv {f : ℂ → ℂ} {A : ℝ} (h : TauCeti.OrderLE f A)
    (hf : Differentiable ℂ f) : TauCeti.OrderLE (deriv f) A := by
  simpa using h.iteratedDeriv hf 1

end TauCeti.OrderLE
