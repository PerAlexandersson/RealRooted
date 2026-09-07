/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Laguerre.Orthogonality

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integral form of generalized Laguerre orthogonality

This file identifies the signed Gamma moment pairing with the classical
positive-half-line integral after substituting `-x` into the sign-reversed
polynomials.
-/

@[expose] public section

open Polynomial Set MeasureTheory

noncomputable section

namespace RealRooted

/-- The positive-half-line integrand represented by the signed Laguerre
moment functional. -/
def generalizedLaguerreIntegrand (α : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.eval (-x) * x ^ α * Real.exp (-x)

/-- The generalized Laguerre integrand is integrable on the positive
half-line in the open classical parameter range. -/
theorem integrableOn_generalizedLaguerreIntegrand
    {α : ℝ} (hα : -1 < α) (p : ℝ[X]) :
    IntegrableOn (generalizedLaguerreIntegrand α p) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      refine (hp.add hq).congr_fun ?_ measurableSet_Ioi
      intro x hx
      simp [generalizedLaguerreIntegrand]
      ring
  | monomial n c =>
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hs : 0 < α + (n : ℝ) + 1 := by linarith
      have hgamma := Real.GammaIntegral_convergent hs
      refine IntegrableOn.congr_fun
        (hgamma.const_mul (c * (-1 : ℝ) ^ n)) ?_ measurableSet_Ioi
      intro x hx
      have hxpos : 0 < x := hx
      rw [generalizedLaguerreIntegrand, eval_monomial]
      have hneg : (-x) ^ n = (-1 : ℝ) ^ n * x ^ n := by
        rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
      rw [hneg]
      dsimp only
      rw [show α + (n : ℝ) + 1 - 1 = (n : ℝ) + α by ring,
        Real.rpow_add hxpos, Real.rpow_natCast]
      ring

/-- The signed Gamma functional is integration against the classical
Laguerre weight after the sign reversal `x ↦ -x`. -/
theorem generalizedLaguerreFunctional_eq_integral
    {α : ℝ} (hα : -1 < α) (p : ℝ[X]) :
    generalizedLaguerreFunctional α p =
      ∫ x in Ioi 0, generalizedLaguerreIntegrand α p x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [generalizedLaguerreFunctional_add, hp, hq,
        ← MeasureTheory.integral_add
          (integrableOn_generalizedLaguerreIntegrand hα p)
          (integrableOn_generalizedLaguerreIntegrand hα q)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp [generalizedLaguerreIntegrand]
      ring
  | monomial n c =>
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hs : 0 < α + (n : ℝ) + 1 := by linarith
      rw [generalizedLaguerreFunctional_monomial,
        generalizedLaguerreMoment, Real.Gamma_eq_integral hs]
      rw [show c * ((-1 : ℝ) ^ n *
          ∫ x in Ioi 0, Real.exp (-x) * x ^ (α + (n : ℝ) + 1 - 1)) =
        (c * (-1 : ℝ) ^ n) *
          ∫ x in Ioi 0, Real.exp (-x) * x ^ (α + (n : ℝ) + 1 - 1) by ring]
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := hx
      rw [generalizedLaguerreIntegrand, eval_monomial]
      have hneg : (-x) ^ n = (-1 : ℝ) ^ n * x ^ n := by
        rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
      rw [hneg, show α + (n : ℝ) + 1 - 1 = (n : ℝ) + α by ring,
        Real.rpow_add hxpos, Real.rpow_natCast]
      ring

/-- The moment pairing is the classical generalized Laguerre integral after
sign reversal. -/
theorem generalizedLaguerreInner_eq_integral
    {α : ℝ} (hα : -1 < α) (p q : ℝ[X]) :
    generalizedLaguerreInner α p q =
      ∫ x in Ioi 0,
        p.eval (-x) * q.eval (-x) * x ^ α * Real.exp (-x) := by
  change generalizedLaguerreFunctional α (p * q) = _
  rw [generalizedLaguerreFunctional_eq_integral hα]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp [generalizedLaguerreIntegrand]

/-- Distinct generalized Laguerre polynomials satisfy the classical integral
orthogonality relation. -/
theorem generalizedLaguerre_integral_orthogonal
    {α : ℝ} (hα : -1 < α) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in Ioi 0,
      (generalizedLaguerre m α).eval (-x) *
        (generalizedLaguerre n α).eval (-x) *
          x ^ α * Real.exp (-x)) = 0 := by
  rw [← generalizedLaguerreInner_eq_integral hα]
  exact generalizedLaguerre_pairwise_orthogonal hα hmn

end RealRooted
