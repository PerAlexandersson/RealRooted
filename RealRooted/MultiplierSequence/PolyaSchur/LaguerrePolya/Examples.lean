import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Laguerre--Pólya examples

This opt-in leaf identifies the exponential as the complex
exponential-generating function of the constant-one multiplier sequence and
therefore supplies checked Laguerre--Pólya and Type-I witnesses.  It also
instantiates the reverse Pólya--Schur classification at this classical example.
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

/-- The complex exponential is Type-I Laguerre--Pólya. -/
theorem isLaguerrePolyaTypeI_exp : IsLaguerrePolyaTypeI Complex.exp := by
  rw [← complexExpGeneratingFunction_one]
  exact isPFMultiplierSequence_one_sequence.isLaguerrePolyaTypeI_complexExpGeneratingFunction

/-- The Type-I Pólya--Schur classification specialized to the complex
exponential and the constant-one sequence. -/
theorem isPFMultiplierSequence_one_iff_isLaguerrePolyaTypeI_exp :
    IsPFMultiplierSequence (fun _ => (1 : ℝ)) ↔
      IsLaguerrePolyaTypeI Complex.exp := by
  rw [← complexExpGeneratingFunction_one]
  apply isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
  refine ⟨1, zero_lt_one, ?_⟩
  simpa using Real.summable_pow_div_factorial (1 : ℝ)

/-- The complex EGF of the constant-negative-one sequence is `-exp`. -/
theorem complexExpGeneratingFunction_neg_one :
    complexExpGeneratingFunction (fun _ => (-1 : ℝ)) =
      fun z => -Complex.exp z := by
  rw [show (fun _ => (-1 : ℝ)) = fun k => (-1 : ℝ) * (fun _ => (1 : ℝ)) k by
    funext k
    simp, complexExpGeneratingFunction_const_mul, complexExpGeneratingFunction_one]
  simp

/-- The negative complex exponential satisfies the checked signed Type-I
classification. -/
theorem isLaguerrePolyaTypeISigned_neg_exp :
    IsLaguerrePolyaTypeISigned (fun z => -Complex.exp z) := by
  rw [← complexExpGeneratingFunction_neg_one]
  apply
    (isMultiplierSequence_iff_isLaguerrePolyaTypeISigned_complexExpGeneratingFunction
      (gamma := fun _ => (-1 : ℝ)) ?_).mp
  · exact isMultiplierSequence_const_sequence (-1)
  · refine ⟨1, zero_lt_one, ?_⟩
    simpa using Real.summable_pow_div_factorial (1 : ℝ)

end RealRooted
