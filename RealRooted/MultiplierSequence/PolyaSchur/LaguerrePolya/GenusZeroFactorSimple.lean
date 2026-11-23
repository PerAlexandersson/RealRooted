module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GenusZeroDifferentialSimple
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialGaussian
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GenusZeroComposition

/-!
# Simplicity for symbols with a nonpolynomial genus-zero factor

This is the factorized Gaussian case in the Cardon--de Gaston simplicity
argument. Extracting such a factor from an arbitrary infinite real zero set
is a separate result. No nonzero intermediate-image premise is needed.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- A nonpolynomial pure genus-zero factor forces the nonzero Gaussian
differential image to have only simple real zeros. -/
theorem IsLaguerrePolya.genusZero_factor_differential_simple_or_zero
    {φ f : ℂ → ℂ} (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f)
    {a : ℕ → ℝ} (ha : Summable a)
    (hnp : ∀ p : ℂ[X],
      (fun z : ℂ ↦ ∏' j, (1 + (a j : ℂ) * z)) ≠ fun z ↦ p.eval z)
    {Mφ Mf A B : ℝ} (hMφ : 0 ≤ Mφ) (hMf : 0 ≤ Mf) (hA : 0 < A) (hB : 0 < B)
    (hAB : 4 * A * B < 1)
    (hφbound : ∀ w, ‖φ w‖ ≤ Mφ * Real.exp (A * ‖w‖ ^ 2))
    (hfbound : ∀ w, ‖f w‖ ≤ Mf * Real.exp (B * ‖w‖ ^ 2)) :
    let H := infiniteDifferentialApply
      (fun z ↦ (∏' j, (1 + (a j : ℂ) * z)) * φ z) f
    H = 0 ∨ IsLaguerrePolya H ∧
      ∀ z, H z = 0 → z.im = 0 ∧ _root_.deriv H z ≠ 0 := by
  have hg := hφ.infiniteDifferentialApply_of_gaussian hf hMφ hMf hA hB hAB
    hφbound hfbound
  have h := hg.genusZero_differential_simple_or_zero ha hnp
  simpa only [infiniteDifferentialApply_linearProduct_mul ha
    hφ.differentiable hf.differentiable hMφ hMf hA hB hAB hφbound hfbound] using h

end RealRooted
