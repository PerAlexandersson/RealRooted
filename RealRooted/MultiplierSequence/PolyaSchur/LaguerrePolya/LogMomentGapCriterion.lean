/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.PFPolynomial
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogMomentGapPolynomial
import RealRooted.PFPolynomial.LogMomentGap
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Const
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Positive logarithmic moment support gaps characterize PF polynomials

This is a derived finite-factor specialization of the normalized Type-I
moment criterion in Sokal (2022), Proposition 6, printed page 5. It is not
an assertion of novelty or an additional theorem attributed to that paper.
-/

public section

open Complex MeasureTheory Polynomial

namespace RealRooted

/-- An entire function nonzero at zero has an actual logarithmic moment
measure with a positive lower support gap exactly when its normalization is
a real PF polynomial. Constants and arbitrary nonzero complex scalar factors
are included. The competing measure requires all moments to be integrable. -/
theorem exists_isPFPolynomial_iff_logDeriv_moments_gap
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    (∃ p : ℝ[X], IsPFPolynomial p ∧ p.coeff 0 = 1 ∧
      ∀ z : ℂ, f z / f 0 = (p.map ofRealHom).eval z) ↔
    ∃ (mu : Measure ℝ) (c : ℝ), 0 < c ∧ (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
        (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) 0 / k.factorial =
          ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) := by
  constructor
  · rintro ⟨p, hp, hp0, heq⟩
    obtain ⟨mu, c, hc, hgap, hmom⟩ := hp.exists_logDeriv_moments_gap hp0
    have hlog : logDeriv (fun z : ℂ => (p.map ofRealHom).eval z) = logDeriv f := by
      rw [← funext heq]
      exact funext fun z => logDeriv_div_const z (f 0) h0
    exact ⟨mu, c, hc, hgap, by simpa only [hlog] using hmom⟩
  · rintro ⟨mu, c, hc, hgap, hmom⟩
    exact exists_isPFPolynomial_of_logDeriv_moments_gap hf h0 hc hgap hmom

end RealRooted
