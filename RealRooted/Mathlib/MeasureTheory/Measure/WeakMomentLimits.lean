/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import TauCeti.MeasureTheory.Measure.FiniteMeasure.UniformIntegrable

/-!
# Polynomial moments of weak limits on the nonnegative half-line

If finite measures converge weakly and all their natural moments converge to
finite real values, those values are the moments of the weak limit. The
convergent moment of order `2*k` supplies the uniform-integrability estimate
for the moment of order `k`. No fixed compact support is required.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace MeasureTheory

/-- For an integrable natural power on the nonnegative half-line, the extended
nonnegative integral is the coercion of its real integral. -/
theorem lintegral_pow_eq_ofReal_integral {μ : Measure ℝ≥0} (k : ℕ)
    (h : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) μ) :
    (∫⁻ x : ℝ≥0, (x : ℝ≥0∞) ^ k ∂μ) =
      ENNReal.ofReal (∫ x : ℝ≥0, (x : ℝ) ^ k ∂μ) := by
  simpa only [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow] using
    (ofReal_integral_eq_lintegral_ofReal h
      (.of_forall fun x => pow_nonneg x.coe_nonneg k)).symm

/-- A weak limit of finite measures inherits every convergent natural moment.
Convergence of all moments includes the higher moment needed for uniform
integrability. The zero moment and the zero measure require no separate case. -/
theorem FiniteMeasure.integral_pow_eq_of_tendsto
    {ι : Type*} {L : Filter ι} [NeBot L]
    {μs : ι → FiniteMeasure ℝ≥0} {μ : FiniteMeasure ℝ≥0} {m : ℕ → ℝ}
    (hweak : Tendsto μs L (𝓝 μ))
    (hint : ∀ i k, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) (μs i : Measure ℝ≥0))
    (hlim : ∀ k, Tendsto
      (fun i => ∫ x : ℝ≥0, (x : ℝ) ^ k ∂(μs i : Measure ℝ≥0)) L (𝓝 (m k)))
    (k : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) (μ : Measure ℝ≥0) ∧
      (∫ x : ℝ≥0, (x : ℝ) ^ k ∂(μ : Measure ℝ≥0)) = m k := by
  have hm : 0 ≤ m k := ge_of_tendsto (hlim k)
    (.of_forall fun i => integral_nonneg fun x => pow_nonneg x.coe_nonneg k)
  let C := Real.toNNReal (m (k * 2) + 1)
  have hC : ∀ᶠ i in L,
      ∫⁻ x : ℝ≥0, ((x ^ k : ℝ≥0) : ℝ≥0∞) ^ 2 ∂(μs i : Measure ℝ≥0) ≤ C := by
    filter_upwards [(hlim (k * 2)).eventually
      (gt_mem_nhds (lt_add_one (m (k * 2))))] with i hi
    simp only [ENNReal.coe_pow, ← pow_mul]
    rw [lintegral_pow_eq_ofReal_integral (k * 2) (hint i (k * 2))]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal (m (k * 2) + 1)
    exact ENNReal.ofReal_le_ofReal hi.le
  have hpow := TauCeti.tendsto_lintegral_of_sq_bound
    (show Continuous (fun x : ℝ≥0 => x ^ k) by fun_prop) hweak hC
  have hreal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim k)
  have hlim' : Tendsto
      (fun i => ∫⁻ x : ℝ≥0, ((x ^ k : ℝ≥0) : ℝ≥0∞) ∂(μs i : Measure ℝ≥0))
      L (𝓝 (ENNReal.ofReal (m k))) := by
    convert hreal using 1
    funext i
    simpa only [ENNReal.coe_pow, Function.comp_def] using
      lintegral_pow_eq_ofReal_integral k (hint i k)
  have hvalue : (∫⁻ x : ℝ≥0, ((x ^ k : ℝ≥0) : ℝ≥0∞) ∂(μ : Measure ℝ≥0)) =
      ENNReal.ofReal (m k) := tendsto_nhds_unique hpow hlim'
  have hfinite : HasFiniteIntegral (fun x : ℝ≥0 => ((x ^ k : ℝ≥0) : ℝ))
      (μ : Measure ℝ≥0) := by
    apply hasFiniteIntegral_iff_ofNNReal.mpr
    rw [hvalue]
    exact ENNReal.ofReal_lt_top
  have hi : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) (μ : Measure ℝ≥0) := by
    refine ⟨(by fun_prop), ?_⟩
    simpa only [NNReal.coe_pow] using hfinite
  refine ⟨hi, ?_⟩
  have hvalue' : ENNReal.ofReal (∫ x : ℝ≥0, (x : ℝ) ^ k ∂(μ : Measure ℝ≥0)) =
      ENNReal.ofReal (m k) := by
    rw [← lintegral_pow_eq_ofReal_integral k hi]
    simpa only [ENNReal.coe_pow] using hvalue
  have hnonneg : 0 ≤ ∫ x : ℝ≥0, (x : ℝ) ^ k ∂(μ : Measure ℝ≥0) :=
    integral_nonneg fun x => pow_nonneg x.coe_nonneg k
  simpa only [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal hm] using
    congrArg ENNReal.toReal hvalue'

end MeasureTheory
