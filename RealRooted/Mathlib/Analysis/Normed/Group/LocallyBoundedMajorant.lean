/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import TauCeti.Analysis.Normed.Group.LocallyBounded

/-!
# Local boundedness from a continuous majorant

A continuous real majorant of all norms bounds the family uniformly on every
compact subset of its domain.
-/

public section

/-- A common continuous norm majorant makes a family locally bounded. -/
theorem TauCeti.isLocallyBoundedOn_of_norm_le_continuous
    {ι X E : Type*} [TopologicalSpace X] [Norm E]
    {F : ι → X → E} {g : X → ℝ} {S : Set X}
    (hg : ContinuousOn g S) (hbound : ∀ i, ∀ z ∈ S, ‖F i z‖ ≤ g z) :
    TauCeti.IsLocallyBoundedOn F S := by
  rw [TauCeti.isLocallyBoundedOn_def]
  intro K hKS hK
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (hg.mono hKS)).bddAbove
  exact ⟨C, fun i z hz => (hbound i z (hKS hz)).trans (hC (Set.mem_image_of_mem g hz))⟩
