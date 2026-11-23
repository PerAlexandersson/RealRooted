/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroSum
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Absolute convergence of the integrated zero kernel

The norm is exactly `x^(3/2)` times the multiplicity-weighted reciprocal
quadratic denominator under RH. This is valid for every `x > 0`.
-/

public section

open Complex

namespace RiemannHypothesis

/-- The norm of one integrated zero contribution under RH, with full analytic multiplicity. -/
theorem norm_riemannZeta_order_mul_cpow_div (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 0 < ρ.re) :
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖ =
      x ^ (3 / 2 : ℝ) * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ * (ρ + 1)‖) := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    exact riemannZeta_one_ne_zero (h ▸ hz)
  have hhalf := hRH.re_eq_half_of_riemannZeta_eq_zero_of_re_pos hre hz hρ1
  rw [norm_div, norm_mul, norm_natCast, norm_cpow_eq_rpow_re_of_pos hx,
    add_re, one_re, hhalf]
  norm_num
  ring

/-- The integrated nontrivial-zero series converges absolutely under RH. -/
theorem summable_norm_riemannZeta_order_mul_cpow_div (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} ↦
      ‖(analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
        ((ρ : ℂ) * ((ρ : ℂ) + 1))‖) := by
  exact (hRH.summable_riemannZeta_order_div_norm_mul_add_one.mul_left
    (x ^ (3 / 2 : ℝ))).congr (fun ρ ↦
      (hRH.norm_riemannZeta_order_mul_cpow_div hx ρ.property.1 ρ.property.2).symm)

/-- The integrated nontrivial-zero series is summable under RH. -/
theorem summable_riemannZeta_order_mul_cpow_div (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} ↦
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
        ((ρ : ℂ) * ((ρ : ℂ) + 1))) :=
  (hRH.summable_norm_riemannZeta_order_mul_cpow_div hx).of_norm

end RiemannHypothesis
