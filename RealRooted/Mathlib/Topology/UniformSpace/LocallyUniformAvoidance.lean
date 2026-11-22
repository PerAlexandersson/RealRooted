/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Local avoidance under locally uniform convergence

A value avoided by the continuous limit at one point is eventually avoided
by the approximating functions on a common neighborhood of that point.
-/

public section

open Filter Topology

/-- A locally uniform limit continuous at `x` and different from `b` there
gives a common neighborhood on which the approximants eventually avoid `b`. -/
theorem TendstoLocallyUniformlyOn.exists_eventually_ne
    {α β ι : Type*} [TopologicalSpace α] [MetricSpace β]
    {F : ι → α → β} {f : α → β} {l : Filter ι} {U : Set α} {x : α} {b : β}
    (h : TendstoLocallyUniformlyOn F f l U) (hU : U ∈ 𝓝 x)
    (hf : ContinuousAt f x) (hb : f x ≠ b) :
    ∃ V ∈ 𝓝 x, ∀ᶠ n in l, ∀ y ∈ V, F n y ≠ b := by
  have hd : 0 < dist (f x) b := dist_pos.mpr hb
  obtain ⟨V, hV, hconv⟩ := h _ (Metric.dist_mem_uniformity (half_pos hd)) x
    (mem_of_mem_nhds hU)
  rw [nhdsWithin_eq_nhds.mpr hU] at hV
  have hclose : {y | dist (f y) (f x) < dist (f x) b / 2} ∈ 𝓝 x :=
    hf.eventually (Metric.ball_mem_nhds _ (half_pos hd))
  refine ⟨V ∩ {y | dist (f y) (f x) < dist (f x) b / 2}, inter_mem hV hclose, ?_⟩
  filter_upwards [hconv] with n hn y hy hny
  have h₁ := hn y hy.1
  change dist (f y) (F n y) < dist (f x) b / 2 at h₁
  rw [hny] at h₁
  have h₂ := dist_triangle (f x) (f y) b
  rw [dist_comm (f x) (f y)] at h₂
  have h₃ : dist (f y) (f x) < dist (f x) b / 2 := hy.2
  linarith
