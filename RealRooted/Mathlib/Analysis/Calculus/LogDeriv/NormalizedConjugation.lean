/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Identity
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Convex

/-!
# Real normalization from a real logarithmic derivative

Conjugating both argument and value commutes with logarithmic differentiation.
For an entire function normalized to one at zero, conjugation symmetry of its
logarithmic derivative on the slit plane recovers symmetry of the function.
-/

public section

open Complex Set
open scoped ComplexConjugate

/-- Reflection across the real axis commutes with the totalized logarithmic
derivative, including zeros and points where differentiability fails. -/
theorem Complex.logDeriv_conj_conj (f : ℂ → ℂ) :
    logDeriv (conj ∘ f ∘ conj) = conj ∘ logDeriv f ∘ conj := by
  funext z
  simp only [logDeriv_apply, deriv_conj_conj, Function.comp_apply, map_div₀]

/-- Normalization removes the complex scalar ambiguity when the logarithmic
derivative respects conjugation on the slit plane. -/
theorem Differentiable.conj_of_eqOn_logDeriv_conj
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (hne : ∀ z ∈ slitPlane, f z ≠ 0)
    (hlog : EqOn (conj ∘ logDeriv f ∘ conj) (logDeriv f) slitPlane) :
    ∀ z, f (conj z) = conj (f z) := by
  let g := conj ∘ f ∘ conj
  have hg : Differentiable ℂ g := by
    intro z
    simpa only [g, conj_conj] using (hf (conj z)).conj_conj
  have hgn : ∀ z ∈ slitPlane, g z ≠ 0 := by
    intro z hz hg0
    have hzc : conj z ∈ slitPlane := by
      simpa only [mem_slitPlane_iff, conj_re, conj_im, neg_ne_zero] using hz
    apply hne (conj z) hzc
    simpa only [g, Function.comp_apply, map_zero, conj_conj] using congrArg conj hg0
  have hconn :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have heq := hf.eq_mul_of_logDeriv_eqOn hg isOpen_slitPlane hconn
    ⟨1, one_mem_slitPlane⟩ hne hgn
    (fun z hz ↦ by
      rw [show logDeriv g = conj ∘ logDeriv f ∘ conj from logDeriv_conj_conj f]
      exact (hlog hz).symm)
    (by simp [g, Function.comp_apply, h0])
  intro z
  simpa only [h0, one_mul, g, Function.comp_apply, conj_conj] using heq (conj z)

end
