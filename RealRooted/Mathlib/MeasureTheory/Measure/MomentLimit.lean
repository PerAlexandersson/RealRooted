/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import RealRooted.Mathlib.MeasureTheory.Measure.WeakMomentLimits
import RealRooted.Mathlib.MeasureTheory.Measure.FirstMomentTight
import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Closure of Stieltjes moment sequences under pointwise limits

Convergence of the zeroth and first moments gives mass bounds and tightness.
Prokhorov compactness supplies a weak cluster measure; convergence of all
higher moments makes each polynomial test uniformly integrable. Thus limits
of genuine Stieltjes moment sequences are again genuine Stieltjes moments,
without a common compact support or an analytic growth assumption.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

/-- Limits of all natural moments of finite measures on `ℝ≥0` have a single
finite positive representing measure on `ℝ≥0`. -/
theorem exists_measure_moments_nnreal_of_tendsto
    (μs : ℕ → FiniteMeasure ℝ≥0) (m : ℕ → ℝ)
    (hint : ∀ i k, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) (μs i : Measure ℝ≥0))
    (hlim : ∀ k, Tendsto
      (fun i => ∫ x : ℝ≥0, (x : ℝ) ^ k ∂(μs i : Measure ℝ≥0)) atTop (𝓝 (m k))) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ k : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) μ ∧
        (∫ x : ℝ≥0, (x : ℝ) ^ k ∂μ) = m k := by
  have hmasslim : Tendsto (fun i => ((μs i).mass : ℝ)) atTop (𝓝 (m 0)) := by
    simpa only [pow_zero, integral_const, smul_eq_mul, mul_one,
      Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using hlim 0
  obtain ⟨C0, hC0⟩ := hmasslim.isBoundedUnder_le.bddAbove_range
  have hmass (i : ℕ) : (μs i).mass ≤ C0.toNNReal :=
    NNReal.le_toNNReal_of_coe_le (hC0 (mem_range_self i))
  obtain ⟨C1, hC1⟩ := (hlim 1).isBoundedUnder_le.bddAbove_range
  have hfirst (i : ℕ) : ∫⁻ x : ℝ≥0, (x : ℝ≥0∞) ∂(μs i : Measure ℝ≥0) ≤
      (C1.toNNReal : ℝ≥0∞) := by
    have hid := lintegral_pow_eq_ofReal_integral 1 (hint i 1)
    simp only [pow_one] at hid
    rw [hid]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal C1
    exact ENNReal.ofReal_le_ofReal (by simpa only [pow_one] using hC1 (mem_range_self i))
  have htight : IsTightMeasureSet (range fun i => (μs i : Measure ℝ≥0)) :=
    isTightMeasureSet_of_lintegral_id_le (by rintro _ ⟨i, rfl⟩; exact hfirst i)
  obtain ⟨μ, U, hU, hfin, _, hweak⟩ := TauCeti.finite_measure_cluster_limit
    (fun i => (μs i : Measure ℝ≥0)) C0.toNNReal
    (fun i => by rw [← FiniteMeasure.ennreal_mass]; exact_mod_cast hmass i) htight
  let ν : FiniteMeasure ℝ≥0 := ⟨μ, hfin⟩
  have hweak' : Tendsto μs (U : Filter ℕ) (𝓝 ν) :=
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  refine ⟨μ, hfin, fun k => ?_⟩
  exact FiniteMeasure.integral_pow_eq_of_tendsto hweak' hint
    (fun j => (hlim j).mono_left hU) k

/-- The representing measure in the moment-limit theorem may be regarded as
a real measure carried by `[0,∞)`. -/
theorem exists_nonnegative_measure_moments_of_nnreal_tendsto
    (μs : ℕ → FiniteMeasure ℝ≥0) (m : ℕ → ℝ)
    (hint : ∀ i k, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k) (μs i : Measure ℝ≥0))
    (hlim : ∀ k, Tendsto
      (fun i => ∫ x : ℝ≥0, (x : ℝ) ^ k ∂(μs i : Measure ℝ≥0)) atTop (𝓝 (m k))) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ (∀ᵐ x ∂μ, 0 ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ ∧
        (∫ x : ℝ, x ^ k ∂μ) = m k := by
  obtain ⟨μ, hfin, hmom⟩ := exists_measure_moments_nnreal_of_tendsto μs m hint hlim
  let : IsFiniteMeasure μ := hfin
  let ν := μ.map ((↑) : ℝ≥0 → ℝ)
  refine ⟨ν, inferInstance, ?_, fun k => ⟨?_, ?_⟩⟩
  · exact ae_map_iff measurable_coe_nnreal_real.aemeasurable measurableSet_Ici |>.mpr
      (.of_forall fun x => x.coe_nonneg)
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr (hmom k).1
  · rw [show ν = μ.map ((↑) : ℝ≥0 → ℝ) from rfl,
      integral_map_of_stronglyMeasurable measurable_coe_nnreal_real (by fun_prop)]
    exact (hmom k).2

/-- Pointwise limits of genuine Stieltjes moment sequences are Stieltjes
moment sequences. The approximating supports may grow without bound. -/
theorem exists_nonnegative_measure_moments_of_tendsto
    (μs : ℕ → FiniteMeasure ℝ) (m : ℕ → ℝ)
    (hpos : ∀ i, ∀ᵐ x ∂(μs i : Measure ℝ), 0 ≤ x)
    (hint : ∀ i k, Integrable (fun x : ℝ => x ^ k) (μs i : Measure ℝ))
    (hlim : ∀ k, Tendsto
      (fun i => ∫ x : ℝ, x ^ k ∂(μs i : Measure ℝ)) atTop (𝓝 (m k))) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ (∀ᵐ x ∂μ, 0 ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ ∧
        (∫ x : ℝ, x ^ k ∂μ) = m k := by
  let νs : ℕ → FiniteMeasure ℝ≥0 := fun i =>
    ⟨(μs i : Measure ℝ).map Real.toNNReal, inferInstance⟩
  have hi (i k : ℕ) : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ k)
      (νs i : Measure ℝ≥0) := by
    apply (integrable_map_measure (by fun_prop) measurable_real_toNNReal.aemeasurable).mpr
    apply (hint i k).congr
    filter_upwards [hpos i] with x hx
    simp only [Function.comp_apply, Real.coe_toNNReal x hx]
  have heq (i k : ℕ) :
      (∫ x : ℝ≥0, (x : ℝ) ^ k ∂(νs i : Measure ℝ≥0)) =
        ∫ x : ℝ, x ^ k ∂(μs i : Measure ℝ) := by
    change (∫ x : ℝ≥0, (x : ℝ) ^ k
      ∂(μs i : Measure ℝ).map Real.toNNReal) = _
    rw [integral_map_of_stronglyMeasurable measurable_real_toNNReal (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [hpos i] with x hx
    rw [Real.coe_toNNReal x hx]
  apply exists_nonnegative_measure_moments_of_nnreal_tendsto νs m hi
  intro k
  simpa only [heq] using hlim k

end MeasureTheory
