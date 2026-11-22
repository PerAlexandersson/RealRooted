/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.Rectangle
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.Contour
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroKernel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith

/-!
# The finite smoothed zeta contour and exhaustion of its zeros

The positive left edge `Re s = 9 / 20` avoids the poles of the first-order Riesz
kernel. Under RH it also avoids zeta zeros. A zero-free pair of horizontal
segments therefore suffices to specialize the unconditional weighted residue
formula to the smoothed Perron integrand.

The rectangle zero sums converge to the sum over all positive-real-part zeta
zeros as the height tends to infinity. The exhaustion theorem applies to any
summable weight; the integrated Riesz weight is summable by the existing RH
zero-kernel theorem. All zero sums retain analytic multiplicities.
-/

public section

open Complex Set Filter
open scoped Topology Interval

namespace Complex

/-- The first-order Riesz kernel is analytic on the open positive half-plane. -/
theorem analyticOnNhd_cpow_div_mul_add_one {x : ℂ} (hx : x ≠ 0) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ x ^ (s + 1) / (s * (s + 1)))
      {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  have hs₀ : s ≠ 0 := by
    intro h
    simp [h] at hs
  have hs₁ : s + 1 ≠ 0 := by
    intro h
    have hre : s.re + 1 = 0 := by simpa using congrArg Complex.re h
    linarith
  have hnum : AnalyticAt ℂ (fun z : ℂ ↦ x ^ (z + 1)) s := by
    simp_rw [cpow_def_of_ne_zero hx]
    exact (analyticAt_const.mul (analyticAt_id.add analyticAt_const)).cexp
  exact hnum.div (analyticAt_id.mul (analyticAt_id.add analyticAt_const))
    (mul_ne_zero hs₀ hs₁)

/-- Membership in the symmetric positive-half-plane Perron rectangle. -/
theorem mem_riesz_rectangle_iff {t : ℝ} (ht : 0 ≤ t) {s : ℂ} :
    s ∈ Rectangle ((9 / 20 : ℂ) - I * t) (2 + I * t) ↔
      (9 / 20 ≤ s.re ∧ s.re ≤ 2) ∧ |s.im| ≤ t := by
  have hre : ((9 / 20 : ℂ) - I * t).re ≤ (2 + I * t).re := by norm_num
  have him : ((9 / 20 : ℂ) - I * t).im ≤ (2 + I * t).im := by
    simpa using (neg_le_self ht)
  rw [mem_rectangle_iff hre him]
  norm_num [abs_le]

end Complex

namespace RiemannHypothesis

/-- RH and zero-free horizontal segments make the full positive contour boundary zero-free. -/
theorem riemannZeta_ne_zero_on_riesz_rectangle (hRH : RiemannHypothesis)
    {t : ℝ} (ht : 0 ≤ t)
    (hhor : ∀ σ ∈ Icc (9 / 20 : ℝ) 2, ∀ u : ℝ, |u| = t →
      riemannZeta (σ + I * u) ≠ 0) :
    ∀ s ∈ frontier (Rectangle ((9 / 20 : ℂ) - I * t) (2 + I * t)),
      riemannZeta s ≠ 0 := by
  intro s hs
  have hIm : -t ≤ t := by linarith
  simp only [frontier_rectangle, mem_union, mem_reProdIm, mem_insert_iff,
    mem_singleton_iff] at hs
  norm_num [hIm] at hs
  have heq : s = (s.re : ℂ) + I * s.im := by
    apply Complex.ext <;> simp
  rcases hs with ⟨hre, him | him⟩ | ⟨hre | hre, _⟩
  · rw [heq]
    exact hhor s.re hre s.im (by rw [him, abs_neg, abs_of_nonneg ht])
  · rw [heq]
    exact hhor s.re hre s.im (by rw [him, abs_of_nonneg ht])
  · exact hRH.riemannZeta_ne_zero_of_re_eq_nine_twentieths hre
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)

open scoped Classical in
/-- The finite smoothed contour identity at any symmetric zero-free horizontal height. -/
theorem integral_boundary_riesz_rectangle (hRH : RiemannHypothesis)
    {x t : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hhor : ∀ σ ∈ Icc (9 / 20 : ℝ) 2, ∀ u : ℝ, |u| = t →
      riemannZeta (σ + I * u) ≠ 0) :
    let f : ℂ → ℂ := fun s ↦
      -logDeriv riemannZeta s * (x : ℂ) ^ (s + 1) / (s * (s + 1))
    (∫ σ : ℝ in (9 / 20 : ℝ)..2, f (σ + (-t : ℝ) * I)) -
        (∫ σ : ℝ in (9 / 20 : ℝ)..2, f (σ + (t : ℝ) * I)) +
        I * (∫ u : ℝ in -t..t, f (2 + u * I)) -
        I * (∫ u : ℝ in -t..t, f ((9 / 20 : ℂ) + u * I)) =
      2 * Real.pi * I * ((x : ℂ) ^ (2 : ℕ) / 2 -
        ∑ ρ ∈ (isCompact_rectangle ((9 / 20 : ℂ) - I * t)
          (2 + I * t)).inter_riemannZetaZeros_finite.toFinset,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ (ρ + 1) /
            (ρ * (ρ + 1))) := by
  classical
  have hre : ((9 / 20 : ℂ) - I * t).re ≤ (2 + I * t).re := by norm_num
  have him : ((9 / 20 : ℂ) - I * t).im ≤ (2 + I * t).im := by
    simpa using (neg_le_self ht.le)
  have h1 : (1 : ℂ) ∈ interior (Rectangle ((9 / 20 : ℂ) - I * t) (2 + I * t)) := by
    rw [interior_rectangle hre him]
    norm_num [mem_reProdIm, ht]
  have hg : AnalyticOnNhd ℂ (fun s : ℂ ↦
      (x : ℂ) ^ (s + 1) / (s * (s + 1)))
      (Rectangle ((9 / 20 : ℂ) - I * t) (2 + I * t)) := by
    apply (Complex.analyticOnNhd_cpow_div_mul_add_one
      (Complex.ofReal_ne_zero.mpr hx.ne')).mono
    intro s hs
    have hre := ((mem_riesz_rectangle_iff ht.le).mp hs).1.1
    change 0 < s.re
    linarith
  have h := TauCeti.Contour.integral_boundary_rect_neg_logDeriv_riemannZeta
    hre him h1 hg (hRH.riemannZeta_ne_zero_on_riesz_rectangle ht.le hhor)
  norm_num only [ofReal_div, ofReal_ofNat, sub_re, sub_im, mul_re, mul_im,
    I_re, I_im, ofReal_re, ofReal_im, zero_mul, mul_zero, one_mul, zero_add,
    add_zero, sub_zero, zero_sub, add_re, add_im, one_re, one_im] at h
  simpa only [mul_div_assoc, show (1 : ℂ) + 1 = 2 by norm_num, cpow_ofNat,
    show (9 / 20 : ℂ).re = (9 / 20 : ℝ) by norm_num,
    show (9 / 20 : ℂ).im = (0 : ℝ) by norm_num,
    show (2 : ℂ).re = (2 : ℝ) by norm_num,
    show (2 : ℂ).im = (0 : ℝ) by norm_num,
    ofReal_div, ofReal_ofNat, zero_sub, zero_add, one_mul] using h

open scoped Classical in
/-- Symmetric rectangles exhaust the positive-real-part zeta zeros as their heights
tend to infinity. -/
theorem tendsto_sum_riesz_rectangle_zeros (hRH : RiemannHypothesis)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} {g : ℂ → ℂ}
    (ht : Tendsto t l atTop)
    (hg : Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} ↦ g ρ)) :
    Tendsto (fun i ↦
      ∑ ρ ∈ (isCompact_rectangle ((9 / 20 : ℂ) - I * t i)
        (2 + I * t i)).inter_riemannZetaZeros_finite.toFinset, g ρ) l
      (𝓝 (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re}, g ρ)) := by
  classical
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re}
  let A : ι → Finset ℂ := fun i ↦
    (isCompact_rectangle ((9 / 20 : ℂ) - I * t i)
      (2 + I * t i)).inter_riemannZetaZeros_finite.toFinset
  let S : ι → Finset Z := fun i ↦
    (A i).subtype (fun ρ : ℂ ↦ riemannZeta ρ = 0 ∧ 0 < ρ.re)
  have hS : Tendsto S l atTop := by
    rw [atTop_finset_eq_iInf, tendsto_iInf]
    intro ρ
    rw [tendsto_principal]
    filter_upwards [ht.eventually_ge_atTop |(ρ : ℂ).im|] with i hi
    change ({ρ} : Finset Z) ⊆ S i
    apply Finset.singleton_subset_iff.mpr
    change ρ ∈ (A i).subtype (fun ρ : ℂ ↦ riemannZeta ρ = 0 ∧ 0 < ρ.re)
    apply Finset.mem_subtype.mpr
    change (ρ : ℂ) ∈ (isCompact_rectangle ((9 / 20 : ℂ) - I * t i)
      (2 + I * t i)).inter_riemannZetaZeros_finite.toFinset
    rw [Finite.mem_toFinset]
    have hρ1 : (ρ : ℂ) ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ ρ.property.1)
    have hhalf := hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos
      ρ.property.2 ρ.property.1 hρ1
    refine ⟨(mem_riesz_rectangle_iff ((abs_nonneg _).trans hi)).mpr ?_, ρ.property.1⟩
    exact ⟨by norm_num [hhalf], hi⟩
  apply (hg.hasSum.comp hS).congr'
  filter_upwards [ht.eventually_ge_atTop 0] with i hi
  apply Finset.sum_subtype_of_mem
  intro ρ hρ
  have hρ' := (isCompact_rectangle ((9 / 20 : ℂ) - I * t i)
    (2 + I * t i)).inter_riemannZetaZeros_finite.mem_toFinset.mp hρ
  refine ⟨hρ'.2, ?_⟩
  have hre := ((mem_riesz_rectangle_iff hi).mp hρ'.1).1.1
  linarith

open scoped Classical in
/-- The finite integrated zero sums converge to the absolutely convergent RH zero series. -/
theorem tendsto_sum_riesz_rectangle_order_mul_cpow_div (hRH : RiemannHypothesis)
    {ι : Type*} {l : Filter ι} {t : ι → ℝ} (ht : Tendsto t l atTop)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun i ↦
      ∑ ρ ∈ (isCompact_rectangle ((9 / 20 : ℂ) - I * t i)
        (2 + I * t i)).inter_riemannZetaZeros_finite.toFinset,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ (ρ + 1) /
          (ρ * (ρ + 1))) l
      (𝓝 (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re},
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
          ((ρ : ℂ) * ((ρ : ℂ) + 1)))) :=
  hRH.tendsto_sum_riesz_rectangle_zeros ht
    (hRH.summable_riemannZeta_order_mul_cpow_div hx)

end RiemannHypothesis
