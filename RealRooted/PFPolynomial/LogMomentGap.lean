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
import RealRooted.PFPolynomial.FiniteProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LinearProductMomentMeasure
import RealRooted.Mathlib.MeasureTheory.Measure.AtomicGap
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Positive logarithmic moment gaps for normalized PF polynomials
-/

public section

open Complex MeasureTheory Polynomial

namespace RealRooted

/-- A real PF polynomial with constant coefficient one has an actual
logarithmic moment measure with a positive lower support gap. Constant one
is included and gives the zero measure. -/
theorem IsPFPolynomial.exists_logDeriv_moments_gap {p : ℝ[X]}
    (hp : IsPFPolynomial p) (h0 : p.coeff 0 = 1) :
    ∃ (mu : Measure ℝ) (c : ℝ), 0 < c ∧ (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu ∧
        (-1 : ℂ) ^ k * iteratedDeriv k
          (logDeriv (fun z : ℂ => (p.map ofRealHom).eval z)) 0 / k.factorial =
            ((∫ x : ℝ, x ^ k ∂mu : ℝ) : ℂ) := by
  classical
  obtain ⟨a, ha, hfin, heq⟩ := hp.exists_finite_support_tprod h0
  have hs : Summable a := summable_of_ne_finset_zero (s := hfin.toFinset) (by
    intro i hi
    by_contra hne
    exact hi (hfin.mem_toFinset.mpr hne))
  obtain ⟨c, hc, hgap⟩ := exists_pos_ae_le_sum_smul_dirac_of_finite_support ha hfin
  refine ⟨Measure.sum (fun i => ENNReal.ofReal (a i) • Measure.dirac (a i)),
    c, hc, hgap, fun k => ?_⟩
  simpa only [funext heq] using logDeriv_tprod_moments_sum_smul_dirac ha hs k

end RealRooted
