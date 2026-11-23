module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import RealRooted.MultiplierSequence.JensenBessel
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.FormalJensen
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Tactic.Ring

/-!
# The regularized Bessel auxiliary in the Laguerre--Pólya class

O'Sullivan's Section 3.3 auxiliary is the entire function
`regularizedHGFun 0 {alpha + 1} (-z)`. Its reciprocal-Gamma Taylor data
avoid the branch and zero-point issues in the square-root Bessel expression.
The full parameter range `alpha >= -2` follows from the checked Laguerre
splitting theorem and formal Jensen characterization.
-/

public section

open Complex

namespace RealRooted

/-- The reciprocal-Gamma exponential generating series equals the actual
regularized hypergeometric function at every complex argument and real parameter. -/
theorem complexExpGeneratingFunction_inv_gamma_eq (alpha : ℝ) :
    complexExpGeneratingFunction
      (fun k ↦ (-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹) =
        fun z ↦ regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} (-z) := by
  rw [complexExpGeneratingFunction_eq_tsum]
  funext z
  rw [← (hasSum_regularizedHGFun (a := 0) (b := {((alpha + 1 : ℝ) : ℂ)})
    (by simp) (-z)).tsum_eq]
  apply tsum_congr
  intro k
  rw [regularizedHGFunCoeff_zero_singleton]
  have harg : ((alpha + 1 : ℝ) : ℂ) + (k : ℂ) = ((alpha + k + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Gamma_ofReal]
  push_cast
  rw [neg_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The regularized Bessel auxiliary is Laguerre--Pólya throughout the
extended Laguerre parameter range, including `alpha = -1` and `alpha = -2`. -/
theorem isLaguerrePolya_regularized_bessel {alpha : ℝ} (halpha : -2 ≤ alpha) :
    IsLaguerrePolya (fun z ↦ regularizedHGFun 0 {((alpha + 1 : ℝ) : ℂ)} (-z)) := by
  rw [← complexExpGeneratingFunction_inv_gamma_eq]
  exact isLaguerrePolya_of_jensenPolynomial_splits _
    (fun d ↦ jensenPolynomial_inv_gamma_splits d halpha)

end RealRooted
