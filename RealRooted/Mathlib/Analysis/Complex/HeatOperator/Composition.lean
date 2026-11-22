/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Nonzero
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Composition of entire heat operators

The Taylor expansion in the time variable proves the heat composition law for
every pair of complex times. It also proves convergence of the outer heat
series without a separate growth estimate for the intermediate heat image.
Opposite times give inverse operators on entire inputs of order below two.
-/

public section

namespace Complex

/-- The heat series of an intermediate heat image sums to the heat image at
the sum of the two complex times. -/
theorem hasSum_heatOperator_heatOperator {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    (s t z : ℂ) :
    HasSum (fun n : ℕ => (-s) ^ n / (n.factorial : ℂ) *
      iteratedDeriv (2 * n) (heatOperator t f) z) (heatOperator (s + t) f z) := by
  have h := hasSum_taylorSeries_of_entire
    (differentiable_heatOperator_time hf horder hρ z) t (s + t)
  convert h using 1
  ext n
  rw [iteratedDeriv_heatOperator_time hf horder hρ,
    iteratedDeriv_heatOperator hf horder hρ]
  simp only [add_sub_cancel_right, smul_eq_mul]
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

/-- Complex heat times add under composition. -/
theorem heatOperator_heatOperator {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    (s t : ℂ) : heatOperator s (heatOperator t f) = heatOperator (s + t) f := by
  ext z
  exact (hasSum_heatOperator_heatOperator hf horder hρ s t z).tsum_eq

/-- The heat image can be recovered at the opposite complex time. -/
theorem heatOperator_neg_heatOperator {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    (t : ℂ) : heatOperator (-t) (heatOperator t f) = f := by
  rw [heatOperator_heatOperator hf horder hρ, neg_add_cancel, heatOperator_zero]

/-- At any fixed complex time the heat operator distinguishes entire inputs
of order below two. The two order bounds may be different. -/
theorem heatOperator_eq_iff {f g : ℂ → ℂ} {ρ σ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    (hg : Differentiable ℂ g) (horderg : TauCeti.OrderLE g σ) (hσ : σ < 2)
    (t : ℂ) : heatOperator t f = heatOperator t g ↔ f = g := by
  constructor
  · intro h
    have heq := congrArg (heatOperator (-t)) h
    simpa only [heatOperator_neg_heatOperator hf horder hρ,
      heatOperator_neg_heatOperator hg horderg hσ] using heq
  · rintro rfl
    rfl

end Complex
