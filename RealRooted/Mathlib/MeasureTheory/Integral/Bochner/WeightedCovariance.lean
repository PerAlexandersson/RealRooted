/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.TypeStar

/-!
# A weighted covariance identity

The symmetrized double integral is expressed using four ordinary integrals.
The weight and the two functions may be real or complex, with no positivity
hypotheses.
-/

public section

open MeasureTheory

namespace MeasureTheory

variable {α 𝕜 : Type*} [RCLike 𝕜] {w f g : α → 𝕜}

private theorem weight_mul_sub_mul_sub_eq (x y : α) :
    w x * w y * (f y - f x) * (g y - g x) =
      w x * (w y * f y * g y) - (w x * f x) * (w y * g y) -
        (w x * g x) * (w y * f y) + (w x * f x * g x) * w y := by
  ring

variable [MeasurableSpace α] {μ : Measure α}

/-- Four weighted integrability hypotheses suffice for the covariance kernel. -/
theorem integrable_weight_mul_sub_mul_sub
    (hw : Integrable w μ) (hwf : Integrable (fun x => w x * f x) μ)
    (hwg : Integrable (fun x => w x * g x) μ)
    (hwfg : Integrable (fun x => w x * f x * g x) μ) :
    Integrable (fun z : α × α => w z.1 * w z.2 * (f z.2 - f z.1) *
      (g z.2 - g z.1)) (μ.prod μ) := by
  have h := (((hw.mul_prod hwfg).sub (hwf.mul_prod hwg)).sub
    (hwg.mul_prod hwf)).add (hwfg.mul_prod hw)
  convert h using 1
  funext z
  exact weight_mul_sub_mul_sub_eq z.1 z.2

variable [SFinite μ]

/-- The weighted covariance equals half its symmetrized double integral. -/
theorem integral_weight_mul_sub_mul_sub
    (hw : Integrable w μ) (hwf : Integrable (fun x => w x * f x) μ)
    (hwg : Integrable (fun x => w x * g x) μ)
    (hwfg : Integrable (fun x => w x * f x * g x) μ) :
    (∫ z : α × α, w z.1 * w z.2 * (f z.2 - f z.1) *
      (g z.2 - g z.1) ∂μ.prod μ) =
      2 * ((∫ x, w x ∂μ) * (∫ x, w x * f x * g x ∂μ) -
        (∫ x, w x * f x ∂μ) * (∫ x, w x * g x ∂μ)) := by
  simp_rw [weight_mul_sub_mul_sub_eq]
  have hsub : Integrable (fun z : α × α =>
      w z.1 * (w z.2 * f z.2 * g z.2) -
        (w z.1 * f z.1) * (w z.2 * g z.2)) (μ.prod μ) := by
    simpa only [Pi.sub_def] using (hw.mul_prod hwfg).sub (hwf.mul_prod hwg)
  have hsub₂ : Integrable (fun z : α × α =>
      w z.1 * (w z.2 * f z.2 * g z.2) -
        (w z.1 * f z.1) * (w z.2 * g z.2) -
          (w z.1 * g z.1) * (w z.2 * f z.2)) (μ.prod μ) := by
    simpa only [Pi.sub_def] using hsub.sub (hwg.mul_prod hwf)
  rw [integral_add hsub₂ (hwfg.mul_prod hw),
    integral_sub hsub (hwg.mul_prod hwf),
    integral_sub (hw.mul_prod hwfg) (hwf.mul_prod hwg)]
  rw [integral_prod_mul w (fun x => w x * f x * g x),
    integral_prod_mul (fun x => w x * f x) (fun x => w x * g x),
    integral_prod_mul (fun x => w x * g x) (fun x => w x * f x),
    integral_prod_mul (fun x => w x * f x * g x) w]
  ring

end MeasureTheory
