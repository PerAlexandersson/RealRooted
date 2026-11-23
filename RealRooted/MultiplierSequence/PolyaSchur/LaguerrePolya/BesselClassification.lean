module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Bessel
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.BesselTaylor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.BesselInteger
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
import RealRooted.MultiplierSequence.JensenBesselObstruction

/-!
# Exact real parameter range of the regularized Bessel auxiliary

The Laguerre--Pólya parameters are precisely `alpha >= -2` together with all
negative integers. This extends the range used in O'Sullivan's Section 3.3.
The integer cases use the actual entire regularization at Gamma poles.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- The nonintegral parameters below `-2` do not give Laguerre--Pólya
functions, as witnessed by their quadratic Jensen polynomial. -/
theorem not_isLaguerrePolya_regularized_bessel {alpha : ℝ}
    (halpha : alpha < -2) (hnat : ∀ n : ℕ, alpha ≠ -(n : ℝ)) :
    ¬ IsLaguerrePolya
      (fun z ↦ regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} (-z)) := by
  intro hf
  apply not_splits_jensenPolynomial_inv_gamma_two halpha hnat
  simpa only [iteratedDeriv_regularized_bessel_zero, ofReal_re] using
    hf.jensenPolynomial_splits 2

/-- Exact classification, including all negative integer exceptional
parameters and both boundary points `-1` and `-2`. -/
theorem isLaguerrePolya_regularized_bessel_iff (alpha : ℝ) :
    IsLaguerrePolya (fun z ↦ regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} (-z)) ↔
      -2 ≤ alpha ∨ ∃ n : ℕ, alpha = -(n : ℝ) := by
  constructor
  · intro hf
    by_cases ha : -2 ≤ alpha
    · exact Or.inl ha
    by_cases hn : ∃ n : ℕ, alpha = -(n : ℝ)
    · exact Or.inr hn
    exact (not_isLaguerrePolya_regularized_bessel (lt_of_not_ge ha)
      (not_exists.mp hn) hf).elim
  · rintro (ha | ⟨n, rfl⟩)
    · exact isLaguerrePolya_regularized_bessel ha
    · exact isLaguerrePolya_regularized_bessel_neg_nat n

/-- The reciprocal-Gamma Jensen family has exactly the same parameter
classification. At exceptional integers its initial rows may be zero. -/
theorem jensenPolynomial_inv_gamma_splits_iff (alpha : ℝ) :
    (∀ d, (jensenPolynomial d
      (fun k ↦ (-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹)).Splits) ↔
      -2 ≤ alpha ∨ ∃ n : ℕ, alpha = -(n : ℝ) := by
  rw [← isLaguerrePolya_regularized_bessel_iff]
  have hf : Differentiable ℂ
      (fun z ↦ regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} (-z)) := by
    intro z
    exact ((analyticAt_regularizedHGFun_zero (-z)).differentiableAt.comp z
      (by fun_prop))
  exact (isLaguerrePolya_iff_jensenPolynomial_splits hf
    (iteratedDeriv_regularized_bessel_zero alpha)).symm

end RealRooted
