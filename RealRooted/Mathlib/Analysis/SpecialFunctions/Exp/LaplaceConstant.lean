/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.MeasureTheory.Integral.Exp.Decay
import Mathlib.Tactic.Ring

/-!
# Laplace moments after adding a constant to a heat trace

A constant spectral term contributes the corresponding factorial reciprocal
power at positive Laplace parameters. Parameter zero is excluded because
the added nonzero constant need not be integrable there.
-/

public section

open MeasureTheory

namespace Real

/-- At positive Laplace parameters, a constant heat contribution has the
usual integrable factorial reciprocal moment. -/
theorem laplace_constant (c : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ k * c) (Set.Ioi 0) ∧
      (∫ t : ℝ in Set.Ioi 0, exp (-x * t) * t ^ k * c) =
        c * (k.factorial : ℝ) / x ^ (k + 1) := by
  have heq : (fun t : ℝ ↦ exp (-x * t) * t ^ k * c) =
      (fun t ↦ c * (t ^ k * exp (-(x * t)))) := by
    funext t
    rw [neg_mul]
    ring
  rw [heq]
  refine ⟨(TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi k hx).const_mul c, ?_⟩
  rw [integral_const_mul, TauCeti.integral_pow_mul_exp_neg_mul_Ioi k hx]
  ring

/-- Adding a constant to an integrable heat trace adds its explicit
factorial reciprocal term to each positive-parameter Laplace moment. -/
theorem laplace_const_add {H : ℝ → ℝ} (c : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x)
    (hH : IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ k * H t) (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ ↦ exp (-x * t) * t ^ k * (c + H t)) (Set.Ioi 0) ∧
      (∫ t : ℝ in Set.Ioi 0, exp (-x * t) * t ^ k * (c + H t)) =
        c * (k.factorial : ℝ) / x ^ (k + 1) +
          ∫ t : ℝ in Set.Ioi 0, exp (-x * t) * t ^ k * H t := by
  have heq : (fun t : ℝ ↦ exp (-x * t) * t ^ k * (c + H t)) =
      (fun t ↦ exp (-x * t) * t ^ k * c) +
        (fun t ↦ exp (-x * t) * t ^ k * H t) := by
    funext t
    exact mul_add _ _ _
  rw [heq]
  obtain ⟨hc, hval⟩ := laplace_constant c k hx
  exact ⟨hc.add hH, (integral_add hc hH).trans (congrArg (· + _) hval)⟩

end Real
