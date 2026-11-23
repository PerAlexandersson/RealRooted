/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Contour.Residue.Basic
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.Order
import RealRooted.Mathlib.Analysis.Contour.Residue.LogDeriv
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# Residues of weighted zeta logarithmic derivatives

For an analytic weight `g`, the residue of `-ζ'/ζ * g` is `g(1)` at the pole
of zeta and `-m g(ρ)` at a zero of multiplicity `m`. Regular points contribute
zero. These unconditional identities retain the full multiplicities.
-/

public section

namespace TauCeti.Contour

/-- Away from the pole of zeta, the residue of its weighted negative logarithmic
derivative is the negative analytic multiplicity times the weight. -/
theorem residue_neg_logDeriv_riemannZeta_mul {g : ℂ → ℂ} {s : ℂ}
    (hs : s ≠ 1) (hg : AnalyticAt ℂ g s) :
    residue (fun z ↦ -logDeriv riemannZeta z * g z) s =
      -(analyticOrderNatAt riemannZeta s : ℂ) * g s := by
  have heq : (fun z ↦ -logDeriv riemannZeta z * g z) =
      (fun z ↦ (-1 : ℂ) * (logDeriv riemannZeta z * g z)) := by
    funext z
    ring
  rw [heq, residue_const_mul,
    residue_logDeriv_mul (meromorphic_riemannZeta s)
      (meromorphicOrderAt_riemannZeta_of_ne_one hs) hg]
  push_cast
  ring

/-- The pole of zeta contributes the weight at `1` to its weighted negative
logarithmic derivative. -/
theorem residue_neg_logDeriv_riemannZeta_mul_one {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 1) :
    residue (fun z ↦ -logDeriv riemannZeta z * g z) 1 = g 1 := by
  have heq : (fun z ↦ -logDeriv riemannZeta z * g z) =
      (fun z ↦ (-1 : ℂ) * (logDeriv riemannZeta z * g z)) := by
    funext z
    ring
  rw [heq, residue_const_mul,
    residue_logDeriv_mul (meromorphic_riemannZeta 1) meromorphicOrderAt_riemannZeta_one hg]
  norm_num

end TauCeti.Contour
