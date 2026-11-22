/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Locally uniform continuity of heat images in time

Convergence of complex times gives locally uniform convergence of the
corresponding spatial heat images. This follows from joint continuity and
compactness of each bounded spatial set.
-/

public section

open Filter Topology

namespace Complex

/-- Convergent complex heat times give locally uniform convergence in space. -/
theorem tendstoLocallyUniformly_heatOperator_of_tendsto {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    {ι : Type*} {l : Filter ι} {t : ι → ℂ} {s : ℂ} (ht : Tendsto t l (𝓝 s)) :
    TendstoLocallyUniformly (fun i => heatOperator (t i) f) (heatOperator s f) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hc : Continuous (fun p : ℂ × K => heatOperator p.1 f p.2) :=
    (continuous_heatOperator hf horder hρ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  intro u hu
  exact ht.eventually
    (Continuous.tendstoUniformly (fun t (z : K) => heatOperator t f z) hc s u hu)

end Complex
