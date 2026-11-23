/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogMomentGapPolynomial


/-!
# Nonpolynomial entire functions exclude positive logarithmic moment gaps
-/

public section

open Complex MeasureTheory Polynomial Set

namespace RealRooted

/-- Every actual logarithmic moment measure of a nonpolynomial entire function
nonzero at zero has positive mass below every positive threshold. No growth
or compact-support assumption is needed. -/
theorem measure_Iio_pos_of_logDeriv_moments_nonpolynomial
    {f : ℂ → ℂ} {mu : Measure ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hpoly : ∀ p : ℂ[X], f ≠ fun z => p.eval z)
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
      (-1 : ℂ) ^ k * iteratedDeriv k (logDeriv f) 0 / k.factorial =
        ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ))
    {c : ℝ} (hc : 0 < c) : 0 < mu (Iio c) := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hgap : ∀ᵐ x ∂mu, c ≤ x := ae_iff.mpr (by
    simpa only [not_le, Set.Iio_def] using hzero)
  obtain ⟨p, -, -, heq⟩ :=
    exists_isPFPolynomial_of_logDeriv_moments_gap hf h0 hc hgap hmom
  apply hpoly (C (f 0) * p.map ofRealHom)
  funext z
  simpa only [eval_mul, eval_C, mul_comm] using (div_eq_iff h0).mp (heq z)

end RealRooted
