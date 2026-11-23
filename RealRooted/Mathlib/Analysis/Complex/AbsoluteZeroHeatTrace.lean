/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import RealRooted.Mathlib.Analysis.SpecialFunctions.Exp.ExponentialSumLaplace
import Mathlib.Analysis.Complex.CauchyIntegral
public import RealRooted.Mathlib.Analysis.Complex.ZeroSpectralIndex
import TauCeti.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Unconditional heat estimates from absolute zero moduli

The trace based on absolute zero moduli is completely monotone for every
finite-order entire function nonzero at the origin. These spectral facts
do not require real zeros or RH. The conditional content of the xi results
is the identification of these Laplace moments with its actual logarithmic
derivatives, which additionally uses the negative-real-zero structure.
-/

public section

open Filter MeasureTheory Topology

namespace Complex

/-- Ordinary real derivatives of the native absolute-zero trace equal
the signed spectral moment sums. -/
theorem iteratedDeriv_zeroHeatTrace_of_order {f : ℂ → ℂ} {rho p t : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (horder : TauCeti.OrderLE f rho)
    (hp : rho < p) (hp0 : 0 ≤ p) (k : ℕ) (ht : 0 < t) :
    iteratedDeriv k (zeroHeatTrace f) t =
      (-1 : ℝ) ^ k * Real.exponentialMomentSum (zeroSpectralRate f) k t := by
  have heq : zeroHeatTrace f =ᶠ[𝓝 t]
      Real.exponentialMomentSum (zeroSpectralRate f) 0 :=
    Filter.Eventually.mono (isOpen_Ioi.mem_nhds ht) fun _ hy ↦
      zeroHeatTrace_eq_exponentialMomentSum hf h0 horder hp hp0 hy
  rw [heq.iteratedDeriv_eq k]
  exact Real.iteratedDeriv_exponentialMomentSum_zero (zeroSpectralRate_pos hf h0) hp0
    (summable_zeroSpectralRate_rpow_neg hf horder hp) k ht

/-- A nonempty native spectrum makes every alternating heat derivative
strictly positive, without any assumption on the arguments of the zeros. -/
theorem signed_iteratedDeriv_zeroHeatTrace_pos_of_order
    {f : ℂ → ℂ} {rho : ℝ} [Nonempty (zeroSpectralIndex f)]
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (horder : TauCeti.OrderLE f rho)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (-1 : ℝ) ^ k * iteratedDeriv k (zeroHeatTrace f) t := by
  let p : ℝ := max rho 0 + 1
  have hp : rho < p := by dsimp [p]; linarith [le_max_left rho 0]
  have hp0 : 0 ≤ p := by dsimp [p]; linarith [le_max_right rho 0]
  rw [iteratedDeriv_zeroHeatTrace_of_order hf h0 horder hp hp0 k ht,
    ← mul_assoc, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow]
  exact Real.exponentialMomentSum_pos (zeroSpectralRate_pos hf h0) hp0
    (summable_zeroSpectralRate_rpow_neg hf horder hp) k ht

/-- Complete monotonicity of the absolute-zero heat trace is unconditional
for finite-order entire functions nonzero at zero. -/
theorem isCompletelyMonotoneOnIoi_zeroHeatTrace_of_order
    {f : ℂ → ℂ} {rho : ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (horder : TauCeti.OrderLE f rho) :
    TauCeti.IsCompletelyMonotoneOnIoi (zeroHeatTrace f) := by
  let p : ℝ := max rho 0 + 1
  have hp : rho < p := by dsimp [p]; linarith [le_max_left rho 0]
  have hp0 : 0 ≤ p := by dsimp [p]; linarith [le_max_right rho 0]
  apply (Real.isCompletelyMonotoneOnIoi_exponentialMomentSum
    (zeroSpectralRate_pos hf h0) hp0
    (summable_zeroSpectralRate_rpow_neg hf horder hp) 0).congr
  intro t ht
  exact zeroHeatTrace_eq_exponentialMomentSum hf h0 horder hp hp0 ht

/-- Every exponent above the actual order controls the absolute-zero
heat trace near zero, without a real-zero hypothesis. -/
theorem isBigO_iteratedDeriv_zeroHeatTrace_nhdsWithin_of_order
    {f : ℂ → ℂ} {rho p : ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (horder : TauCeti.OrderLE f rho) (hp : rho < p) (hp0 : 0 ≤ p) (k : ℕ) :
    (iteratedDeriv k (zeroHeatTrace f)) =O[𝓝[>] (0 : ℝ)]
      (fun t ↦ t ^ (-(p + (k : ℝ)))) := by
  have hb := Real.isBigO_iteratedDeriv_exponentialMomentSum_zero_nhdsWithin
    (zeroSpectralRate_pos hf h0) hp0
    (summable_zeroSpectralRate_rpow_neg hf horder hp) k
  apply hb.congr' _ (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [iteratedDeriv_zeroHeatTrace_of_order hf h0 horder hp hp0 k ht,
    Real.iteratedDeriv_exponentialMomentSum_zero (zeroSpectralRate_pos hf h0) hp0
      (summable_zeroSpectralRate_rpow_neg hf horder hp) k ht]

/-- Nonvanishing at the origin supplies a common positive lower bound for
all absolute zero moduli, by continuity alone. -/
theorem exists_pos_le_zeroSpectralRate {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ ∀ i : zeroSpectralIndex f, b ≤ zeroSpectralRate f i := by
  obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff.mp
    (hf.continuous.continuousAt.eventually_ne h0)
  refine ⟨b, hb, fun i ↦ ?_⟩
  by_contra hn
  have hzero : f (i.1 : ℂ) = 0 :=
    (hf.analyticAt _).apply_eq_zero_of_divisor_ne_zero i.1.property
  exact (hball (by
    simpa only [dist_zero_right, zeroSpectralRate] using lt_of_not_ge hn)) hzero

/-- A common positive exponential rate controls every absolute-zero heat
derivative at large time, independently of the locations' arguments. -/
theorem exists_isBigO_iteratedDeriv_zeroHeatTrace_atTop_of_order
    {f : ℂ → ℂ} {rho : ℝ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (horder : TauCeti.OrderLE f rho) :
    ∃ b : ℝ, 0 < b ∧ ∀ k : ℕ,
      (iteratedDeriv k (zeroHeatTrace f)) =O[atTop] (fun t ↦ Real.exp (-b * t)) := by
  obtain ⟨b, hb, hbound⟩ := exists_pos_le_zeroSpectralRate hf h0
  let p : ℝ := max rho 0 + 1
  have hp : rho < p := by dsimp [p]; linarith [le_max_left rho 0]
  have hp0 : 0 ≤ p := by dsimp [p]; linarith [le_max_right rho 0]
  refine ⟨b, hb, fun k ↦ ?_⟩
  have hg := Real.isBigO_iteratedDeriv_exponentialMomentSum_zero_atTop
    (zeroSpectralRate_pos hf h0) hp0
    (summable_zeroSpectralRate_rpow_neg hf horder hp) hbound k
  apply hg.congr' _ (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [iteratedDeriv_zeroHeatTrace_of_order hf h0 horder hp hp0 k ht,
    Real.iteratedDeriv_exponentialMomentSum_zero (zeroSpectralRate_pos hf h0) hp0
      (summable_zeroSpectralRate_rpow_neg hf horder hp) k ht]

/-- Below order one, absolute-zero heat traces have integrable Laplace
moments even at the parameter zero; the value is the repeated inverse sum. -/
theorem laplace_zeroHeatTrace_of_order_lt_one {f : ℂ → ℂ} {rho x : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (horder : TauCeti.OrderLE f rho)
    (hrho : rho < 1) (k : ℕ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k * zeroHeatTrace f t) (Set.Ioi 0) ∧
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-x * t) * t ^ k * zeroHeatTrace f t) =
        ∑' i : zeroSpectralIndex f, (k.factorial : ℝ) / (x + zeroSpectralRate f i) ^ (k + 1) := by
  have := countable_zeroSpectralIndex hf h0 horder
  let p : ℝ := (max rho 0 + 1) / 2
  have hm : max rho 0 < 1 := max_lt hrho zero_lt_one
  have hp : rho < p := by dsimp [p]; linarith [le_max_left rho 0]
  have hp0 : 0 ≤ p := by dsimp [p]; linarith [le_max_right rho 0]
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hspec := Real.laplace_exponentialMomentSum_of_inverse_moment
    (zeroSpectralRate_pos hf h0) hp0 hp1
    (summable_zeroSpectralRate_rpow_neg hf horder hp) k hx
  have heq : (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k * zeroHeatTrace f t) =ᵐ[
      volume.restrict (Set.Ioi 0)]
      (fun t : ℝ ↦ Real.exp (-x * t) * t ^ k *
        Real.exponentialMomentSum (zeroSpectralRate f) 0 t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [zeroHeatTrace_eq_exponentialMomentSum hf h0 horder hp hp0 ht]
  exact ⟨hspec.1.congr heq.symm, (integral_congr_ae heq).trans hspec.2⟩

end Complex
