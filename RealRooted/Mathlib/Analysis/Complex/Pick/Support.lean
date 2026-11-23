/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Analysis.Complex.Pick.Boundary

/-!
# Support of Nevanlinna measures at real singularities

Analytic continuation across a real boundary point, with real boundary values,
excludes that point from the support of the representing measure.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

/-- A Nevanlinna measure has no support at a point where the represented function
extends analytically and is real on the real axis. -/
theorem notMem_support_of_nevanlinna_of_analyticAt {F : ℂ → ℂ} {μ : Measure ℝ}
    [IsFiniteMeasure μ] {b c r : ℝ}
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂μ + c)
    (hF : AnalyticAt ℂ F (r : ℂ)) (hreal : ∀ x : ℝ, (F x).im = 0) :
    r ∉ μ.support := by
  obtain ⟨ε, hε, hball⟩ := hF.exists_ball_analyticOnNhd
  have hδ : 0 < ε / 4 := by positivity
  have hsub : (Icc (r - ε / 4) (r + ε / 4) ×ℂ Icc 0 (ε / 4) : Set ℂ) ⊆
      Metric.ball (r : ℂ) ε := by
    intro z hz
    rw [Metric.mem_ball, dist_eq]
    apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
    have hx : |z.re - r| ≤ ε / 4 := abs_le.mpr ⟨by linarith [hz.1.1],
      by linarith [hz.1.2]⟩
    rw [abs_of_nonneg hz.2.1]
    linarith [hz.2.2]
  have hcont : ContinuousOn (fun z => (F z).im)
      (Icc (r - ε / 4) (r + ε / 4) ×ℂ Icc 0 (ε / 4)) := by
    exact continuous_im.comp_continuousOn (hball.continuousOn.mono hsub)
  have hzero := measure_Icc_eq_zero_of_eq_nevanlinnaKernel_add hrep
    (by linarith : r - ε / 4 < r + ε / 4) hδ hcont (fun x _ => hreal x)
  exact Measure.notMem_support_iff_exists.mpr
    ⟨Icc (r - ε / 4) (r + ε / 4), Icc_mem_nhds (by linarith) (by linarith), hzero⟩

/-- The support of a Nevanlinna measure lies in any real exceptional set outside
which the represented function extends analytically with real boundary values. -/
theorem support_subset_of_nevanlinna_of_analyticAt {F : ℂ → ℂ} {μ : Measure ℝ}
    [IsFiniteMeasure μ] {b c : ℝ} {s : Set ℝ}
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = (b : ℂ) * z + ∫ x, nevanlinnaKernel z x ∂μ + c)
    (hF : ∀ r ∉ s, AnalyticAt ℂ F (r : ℂ)) (hreal : ∀ x : ℝ, (F x).im = 0) :
    μ.support ⊆ s := by
  intro r hr
  by_contra hrs
  exact notMem_support_of_nevanlinna_of_analyticAt hrep (hF r hrs) hreal hr

end TauCeti
