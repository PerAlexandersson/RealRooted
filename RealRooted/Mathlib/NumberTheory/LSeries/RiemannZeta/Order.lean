/-
Copyright (c) 2026 Steve Hubbard, RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard, RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Meromorphic.Order
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Orders of the Riemann zeta function

Zeta has finite analytic order away from its pole, and meromorphic order `-1`
at `1`. The proof at the pole uses Tau Ceti's corresponding result for the
completed zeta function and the nonvanishing gamma factor.

The finite analytic-order argument is adapted from Steve Hubbard's `goldbach-lean`,
revision `da5cf9edad7896290771dfcab8feee2906399e3d`,
`entries/dudek2014/LeanLab/PNTPort/ExplicitPsi1/Merom.lean` (Apache-2.0).
-/

public section

open Complex Filter Topology Set

namespace TauCeti

/-- Away from the pole, zeta is not the zero analytic germ. -/
theorem analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have hf : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOn_riemannZeta
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have h2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr
      (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    simp
  exact hf.analyticOrderAt_ne_top_of_isPreconnected hconn (x := 2) (y := s)
    (by simp) (by simpa using hs) h2

/-- Zeta's meromorphic order away from its pole is its finite analytic multiplicity. -/
theorem meromorphicOrderAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    meromorphicOrderAt riemannZeta s = (analyticOrderNatAt riemannZeta s : ℤ) := by
  rw [(analyticOn_riemannZeta s hs).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannZeta_ne_top hs)]
  simp

/-- The Riemann zeta function has a simple pole at `1`. -/
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = (-1 : ℤ) := by
  have heq : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)]
      completedRiemannZeta * (fun s ↦ (Gammaℝ s)⁻¹) := by
    filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero)] with s hs
    rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv, Pi.mul_apply]
  have hG : AnalyticAt ℂ (fun s ↦ (Gammaℝ s)⁻¹) 1 :=
    differentiable_Gammaℝ_inv.analyticAt 1
  have horder : meromorphicOrderAt (fun s ↦ (Gammaℝ s)⁻¹) 1 = 0 := by
    rw [hG.meromorphicOrderAt_eq, hG.analyticOrderAt_eq_zero.mpr (by simp [Gammaℝ_one])]
    simp
  rw [meromorphicOrderAt_congr heq,
    meromorphicOrderAt_mul (meromorphic_completedRiemannZeta 1) hG.meromorphicAt,
    meromorphicOrderAt_completedRiemannZeta_one, horder, add_zero]

/-- Zeta has finite meromorphic order at every point. -/
theorem meromorphicOrderAt_riemannZeta_ne_top (s : ℂ) :
    meromorphicOrderAt riemannZeta s ≠ ⊤ := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [meromorphicOrderAt_riemannZeta_one]
  · simp [meromorphicOrderAt_riemannZeta_of_ne_one hs]

end TauCeti
