/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.Taylor.Integral

/-!
# Continuity of iterated derivatives in a parameter
-/

public section

/-- The iterated derivative in the second scalar coordinate of a jointly
smooth function varies continuously with its first coordinate. -/
theorem ContDiff.continuous_iteratedDeriv_snd_zero {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {n : ℕ} {F : 𝕜 × 𝕜 → E} (hF : ContDiff 𝕜 n F) :
    Continuous (fun x : 𝕜 ↦ iteratedDeriv n (fun z ↦ F (x, z)) 0) := by
  have heq (x : 𝕜) : iteratedDeriv n (fun z ↦ F (x, z)) 0 =
      iteratedFDeriv 𝕜 n F (x, 0) (fun _ ↦ (0, 1)) := by
    have h := hF.contDiffAt.iteratedDeriv_comp_add_smul
      (x := (x, 0)) (y := ((0, 1) : 𝕜 × 𝕜)) (t := 0)
    simpa [Prod.mk_add_mk, smul_eq_mul] using h
  simp_rw [heq]
  exact (continuous_eval_const (fun _ : Fin n ↦ ((0, 1) : 𝕜 × 𝕜))).comp
    (hF.continuous_iteratedFDeriv'.comp (continuous_id.prodMk continuous_const))
