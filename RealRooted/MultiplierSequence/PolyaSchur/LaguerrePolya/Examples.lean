import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Laguerre--Pólya examples

This opt-in leaf identifies the exponential as the complex
exponential-generating function of the constant-one multiplier sequence and
therefore supplies its checked Laguerre--Pólya witness. It uses only the
forward limit bridge; it does not establish a Pólya--Schur classification.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- The complex EGF of the constant-one sequence is the complex exponential. -/
theorem complexExpGeneratingFunction_one :
    complexExpGeneratingFunction (fun _ => (1 : ℝ)) = Complex.exp := by
  rw [complexExpGeneratingFunction_eq_tsum]
  ext z
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  apply tsum_congr
  intro k
  rw [div_eq_mul_inv]
  simp only [one_mul, Complex.ofReal_inv]
  exact mul_comm _ _

/-- The complex exponential has a checked zero-aware Laguerre--Pólya witness
from rescaled Jensen polynomials. -/
theorem isLaguerrePolya_exp : IsLaguerrePolya Complex.exp := by
  rw [← complexExpGeneratingFunction_one]
  apply isMultiplierSequence_one_sequence.isLaguerrePolya_complexExpGeneratingFunction
  intro R _
  simpa using Real.summable_pow_div_factorial R

end RealRooted
