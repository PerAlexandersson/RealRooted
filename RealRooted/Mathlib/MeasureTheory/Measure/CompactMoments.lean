/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Compactness for moment limits

We pass limits of continuous test integrals to a finite positive measure on
a compact space. In particular, coefficientwise limits of moments of measures
on a fixed compact interval have a positive-measure representation.

The compact-support ultrafilter lemma is adapted from Tau Ceti
`MeasureTheory/Measure/Prokhorov.lean` (Apache-2.0). This is the compactness
step needed by the unpublished manuscript behind RealRooted issue #2185;
it does not identify operator coefficients with moment limits.
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- A family eventually in a compact set converges along its ultrafilter.
Adapted from Tau Ceti `Topology/Compactness/Compact.lean` (Apache-2.0). -/
theorem IsCompact.exists_tendsto_of_eventually_mem
    {α ι : Type*} [TopologicalSpace α] {s : Set α}
    (hs : IsCompact s) {U : Ultrafilter ι} {u : ι → α} (hu : ∀ᶠ i in U, u i ∈ s) :
    ∃ x ∈ s, Tendsto u U (𝓝 x) := by
  obtain ⟨x, hx, h⟩ := hs.ultrafilter_le_nhds' (U.map u) (Ultrafilter.mem_map.2 hu)
  exact ⟨x, hx, by rwa [Ultrafilter.coe_map] at h⟩

namespace MeasureTheory

/-- Finite measures eventually carried by a compact set, with bounded mass,
have a weak ultrafilter limit carried by that set.
Adapted from Tau Ceti `MeasureTheory/Measure/Prokhorov.lean` (Apache-2.0). -/
theorem exists_tendsto_finiteMeasure_of_eventually_measure_compl_eq_zero
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [T2Space α] [BorelSpace α] {U : Ultrafilter ι}
    {μs : ι → FiniteMeasure α} {K : Set α} (hK : IsCompact K) {C : ℝ}
    (h : ∀ᶠ i in U, (μs i : Measure α) Kᶜ = 0 ∧ (μs i : Measure α).real univ ≤ C) :
    ∃ μ : FiniteMeasure α, (μ : Measure α) Kᶜ = 0 ∧ Tendsto μs U (𝓝 μ) := by
  obtain ⟨μ, ⟨-, hμK⟩, hμ⟩ := IsCompact.exists_tendsto_of_eventually_mem
    (isCompact_setOfPred_finiteMeasure_le_of_isCompact C.toNNReal hK) <| h.mono fun i hi =>
      ⟨NNReal.le_toNNReal_of_coe_le (FiniteMeasure.measureReal_eq_coe_coeFn.symm.trans_le hi.2),
        (FiniteMeasure.null_iff_toMeasure_null _ _).2 hi.1⟩
  exact ⟨μ, (FiniteMeasure.null_iff_toMeasure_null _ _).1 hμK, hμ⟩

/-- Limits of any family of continuous test integrals on a compact space
are represented by a single finite positive measure, provided masses are
uniformly bounded. The index set of tests need not be countable. -/
theorem exists_finiteMeasure_integral_eq_of_tendsto
    {α κ : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [T2Space α] [BorelSpace α] [CompactSpace α]
    (μs : ℕ → FiniteMeasure α) (f : κ → C(α, ℝ)) (m : κ → ℝ)
    {C : ℝ≥0} (hmass : ∀ i, (μs i).mass ≤ C)
    (hlim : ∀ k, Tendsto (fun i => ∫ x, f k x ∂(μs i : Measure α))
      atTop (𝓝 (m k))) :
    ∃ μ : FiniteMeasure α, μ.mass ≤ C ∧
      ∀ k, (∫ x, f k x ∂(μ : Measure α)) = m k := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨μ, hμ, ht⟩ := IsCompact.exists_tendsto_of_eventually_mem
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace α C)
    (show ∀ᶠ i in U, (μs i).mass ≤ C from .of_forall hmass)
  refine ⟨μ, hμ, fun k => ?_⟩
  have ht' := (FiniteMeasure.continuous_integral_continuousMap (f k)).tendsto μ
  exact tendsto_nhds_unique (ht'.comp ht) ((hlim k).mono_left (Ultrafilter.of_le _))

/-- A coefficientwise limit of moment sequences on a compact interval has
a finite positive representing measure on that same interval. -/
theorem exists_finiteMeasure_moments_Icc_of_tendsto
    {β : ℝ} (μs : ℕ → FiniteMeasure (Icc (0 : ℝ) β)) (m : ℕ → ℝ)
    {C : ℝ≥0} (hmass : ∀ i, (μs i).mass ≤ C)
    (hlim : ∀ k, Tendsto
      (fun i => ∫ x : Icc (0 : ℝ) β, (x : ℝ) ^ k ∂(μs i : Measure _))
      atTop (𝓝 (m k))) :
    ∃ μ : FiniteMeasure (Icc (0 : ℝ) β), μ.mass ≤ C ∧
      ∀ k, (∫ x : Icc (0 : ℝ) β, (x : ℝ) ^ k ∂(μ : Measure _)) = m k := by
  exact exists_finiteMeasure_integral_eq_of_tendsto μs
    (fun k => ⟨fun x => (x : ℝ) ^ k, continuous_subtype_val.pow k⟩) m hmass hlim

/-- Moment convergence alone bounds the masses. Consequently a
coefficientwise limit of compact-interval moment sequences is represented by
a finite positive measure on the real line, supported in that interval. -/
theorem exists_measure_moments_Icc_of_tendsto
    {β : ℝ} (μs : ℕ → FiniteMeasure (Icc (0 : ℝ) β)) (m : ℕ → ℝ)
    (hlim : ∀ k, Tendsto
      (fun i => ∫ x : Icc (0 : ℝ) β, (x : ℝ) ^ k ∂(μs i : Measure _))
      atTop (𝓝 (m k))) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ (∀ᵐ x ∂ν, x ∈ Icc 0 β) ∧
      ∀ k, (∫ x : ℝ, x ^ k ∂ν) = m k := by
  have hmasslim : Tendsto (fun i => ((μs i).mass : ℝ)) atTop (𝓝 (m 0)) := by
    simpa [FiniteMeasure.mass] using hlim 0
  obtain ⟨C, hC⟩ := hmasslim.isBoundedUnder_le.bddAbove_range
  have hmass (i : ℕ) : (μs i).mass ≤ C.toNNReal :=
    NNReal.le_toNNReal_of_coe_le (hC (mem_range_self i))
  obtain ⟨μ, -, hμ⟩ := exists_finiteMeasure_moments_Icc_of_tendsto μs m hmass hlim
  let ν : Measure ℝ := (μ : Measure (Icc (0 : ℝ) β)).map Subtype.val
  refine ⟨ν, inferInstance, ?_, fun k => ?_⟩
  · exact ae_map_iff measurable_subtype_coe.aemeasurable
      measurableSet_Icc |>.mpr (ae_of_all _ fun x => x.property)
  · rw [show ν = (μ : Measure (Icc (0 : ℝ) β)).map Subtype.val from rfl,
      integral_map measurable_subtype_coe.aemeasurable (by fun_prop)]
    exact hμ k

end MeasureTheory
