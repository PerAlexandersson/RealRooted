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
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIMomentCriterion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeMeasureUnique
import RealRooted.PFPolynomial.FiniteProduct
import RealRooted.Mathlib.MeasureTheory.Measure.AtomicGap
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Const
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Positive logarithmic moment gaps force PF polynomials

Compact moment uniqueness identifies any given measure with the canonical
slope measure. A positive lower support gap eliminates the exponential term
and leaves only finitely many nonzero slopes. No growth assumption is used.
-/

public section

open Complex MeasureTheory Polynomial

namespace RealRooted

/-- An actual logarithmic moment measure supported above a positive number
forces the normalized entire function to be a real PF polynomial. The measure
is not assumed compact, finite, atomic, or to be the canonical measure. -/
theorem exists_isPFPolynomial_of_logDeriv_moments_gap
    {f : ℂ → ℂ} {mu : Measure ℝ} {c : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hc : 0 < c)
    (hgap : ∀ᵐ x ∂mu, c ≤ x)
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
      (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) 0 / k.factorial =
        ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ)) :
    ∃ p : ℝ[X], IsPFPolynomial p ∧ p.coeff 0 = 1 ∧
      ∀ z : ℂ, f z / f 0 = (p.map ofRealHom).eval z := by
  have hpos : ∀ᵐ x ∂mu, 0 ≤ x := hgap.mono fun _ hx => hc.le.trans hx
  have hF := isLaguerrePolyaTypeI_div_of_logDeriv_moments hf h0 hpos
    (fun k => (hmom k).1) (fun k => (hmom k).2)
  have hF0 : (fun z => f z / f 0) 0 ≠ 0 := div_ne_zero h0 h0
  have hlog : logDeriv (fun z => f z / f 0) = logDeriv f :=
    funext fun z => logDeriv_div_const z (f 0) h0
  have hFm : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
      (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv (fun z => f z / f 0)) 0 /
        k.factorial = ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) := by
    simpa only [hlog] using hmom
  obtain ⟨gamma, a, nu, hg, ha, hs, hprod, hnu, -, -, hnum⟩ :=
    hF.exists_logDeriv_moment_measure_factorization hF0
  have hmunu : mu = nu := (hF.existsUnique_logDeriv_moment_measure hF0).unique hFm hnum
  rw [hmunu, hnu] at hgap
  obtain ⟨hg0, hfin, -⟩ := eq_zero_and_finite_support_of_ae_le_atomic ha hs hg hc hgap
  obtain ⟨p, hp, hp0, hpeval⟩ := exists_isPFPolynomial_eval_eq_tprod ha hfin
  refine ⟨p, hp, hp0, fun z => ?_⟩
  have hz := congrFun hprod z
  simpa only [div_self h0, hg0, ofReal_zero, zero_mul, exp_zero,
    one_mul, ← hpeval z] using hz

end RealRooted
