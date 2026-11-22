/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Residue.LogDeriv

/-!
# Analytically weighted logarithmic derivatives

Multiplying a logarithmic derivative by an analytic weight multiplies its
residue by the value of the weight. Zeros and poles of arbitrary finite order
are included; no simplicity assumption is imposed on the original function.
-/

public section

open Filter Topology

namespace TauCeti.Contour

/-- An analytic weight evaluates at the zero or pole in the residue of a logarithmic
derivative. The integer order includes both zeros and poles. -/
theorem residue_logDeriv_mul {f g : ℂ → ℂ} {z : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z) (hn : meromorphicOrderAt f z = (n : WithTop ℤ))
    (hg : AnalyticAt ℂ g z) :
    residue (fun s ↦ logDeriv f s * g s) z = (n : ℂ) * g z := by
  obtain ⟨u, hu, hu0, heq⟩ := logDeriv_eventuallyEq_principalPart hf hn
  have htail : AnalyticAt ℂ (fun s ↦ logDeriv u s * g s) z := (hu.logDeriv hu0).mul hg
  have hprincipal : MeromorphicAt (fun s ↦ (n : ℂ) * g s / (s - z)) z :=
    (analyticAt_const.mul hg).meromorphicAt.div
      (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hsplit : (fun s ↦ logDeriv f s * g s) =ᶠ[𝓝[≠] z]
      (fun s ↦ (n : ℂ) * g s / (s - z)) + (fun s ↦ logDeriv u s * g s) := by
    filter_upwards [heq] with s hs
    simp only [Pi.add_apply, hs, div_eq_mul_inv]
    ring
  rw [residue_congr_nhdsNE hsplit, residue_add hprincipal htail.meromorphicAt,
    residue_eq_zero_of_analyticAt htail, add_zero]
  simpa using residue_div_sub_pow_of_analyticAt (analyticAt_const.mul hg) 0

end TauCeti.Contour
