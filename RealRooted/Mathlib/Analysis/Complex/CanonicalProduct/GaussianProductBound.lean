/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.MinimalType
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Subquadratic

/-!
# Gaussian type bounds for canonical products

The genus-one part and every subquadratic prefactor use arbitrarily small
quadratic allowances. The actual Gaussian coefficient is retained, including
the coefficient-zero boundary, origin factors, and zero scalar factors.
-/

public section

namespace Complex

/-- A subquadratic prefactor times a real Gaussian and a genus-one product
has a global norm bound with any coefficient above the Gaussian coefficient. -/
theorem exists_norm_gaussian_tprod_le_exp_sq {ι : Type*}
    (a : ι → ℂ) (m : ι → ℕ)
    (hm : Summable (fun i => (m i : ℝ) * ‖a i‖ ^ 2))
    {g : ℂ → ℂ} (hg : Continuous g) {ρ : ℝ}
    (horder : TauCeti.OrderLE g ρ) (hρ : ρ < 2)
    {α : ℝ} (hα : 0 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ,
      ‖g z * exp (-(α : ℂ) * z ^ 2) *
        ∏' i, weierstrassFactor 1 (a i * z) ^ m i‖ ≤
          C * Real.exp ((α + ε) * ‖z‖ ^ 2) := by
  obtain ⟨A, hA, hAbound⟩ := horder.exists_norm_le_mul_exp_sq hg hρ (half_pos hε)
  obtain ⟨B, hB, hBbound⟩ := exists_norm_tprod_weierstrass_le_exp_sq
    a m hm (half_pos hε)
  refine ⟨A * B, mul_pos hA hB, fun z => ?_⟩
  have hgauss : ‖exp (-(α : ℂ) * z ^ 2)‖ ≤ Real.exp (α * ‖z‖ ^ 2) := by
    calc
      _ ≤ Real.exp ‖-(α : ℂ) * z ^ 2‖ := norm_exp_le_exp_norm _
      _ = _ := by
        rw [Complex.norm_mul, norm_neg, norm_pow, norm_real, Real.norm_eq_abs,
          abs_of_nonneg hα]
  calc
    _ = ‖g z‖ * ‖exp (-(α : ℂ) * z ^ 2)‖ *
        ‖∏' i, weierstrassFactor 1 (a i * z) ^ m i‖ := by rw [norm_mul, norm_mul]
    _ ≤ (A * Real.exp (ε / 2 * ‖z‖ ^ 2)) * Real.exp (α * ‖z‖ ^ 2) *
        (B * Real.exp (ε / 2 * ‖z‖ ^ 2)) := by
      gcongr
      · exact hAbound z
      · exact hBbound z
    _ = _ := by
      rw [show (α + ε) * ‖z‖ ^ 2 =
        ε / 2 * ‖z‖ ^ 2 + α * ‖z‖ ^ 2 + ε / 2 * ‖z‖ ^ 2 by ring,
        Real.exp_add, Real.exp_add]
      ring

/-- The literal canonical expression, with arbitrary origin order and scalar,
has arbitrarily sharp Gaussian type. Complex slopes and linear parameters are
allowed; LP membership is not needed for this analytic estimate. -/
theorem exists_norm_canonicalProduct_le_exp_sq {ι : Type*}
    (a : ι → ℂ) (m : ι → ℕ)
    (hm : Summable (fun i => (m i : ℝ) * ‖a i‖ ^ 2))
    (c b : ℂ) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ z : ℂ,
      ‖c * z ^ k * exp (-(α : ℂ) * z ^ 2 + b * z) *
        ∏' i, weierstrassFactor 1 (a i * z) ^ m i‖ ≤
          C * Real.exp ((α + ε) * ‖z‖ ^ 2) := by
  let g : ℂ → ℂ := fun z => c * z ^ k * exp (b * z)
  have hg : Continuous g := by fun_prop
  have ho : TauCeti.OrderLE g 1 := by
    have hp := (Polynomial.orderLE_eval (Polynomial.C c * Polynomial.X ^ k)).mono
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [g, Pi.mul_def, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hp.mul (TauCeti.orderLE_cexp_mul b)
  obtain ⟨C, hC, hbound⟩ := exists_norm_gaussian_tprod_le_exp_sq
    a m hm hg ho (by norm_num) hα hε
  refine ⟨C, hC, fun z => ?_⟩
  convert hbound z using 1
  congr 1
  dsimp only [g]
  rw [exp_add]
  ring

end Complex
