module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MomentResidues
import RealRooted.Mathlib.Analysis.Analytic.CountableZeros
import RealRooted.Mathlib.MeasureTheory.Integral.Bochner.CountableSupport
import RealRooted.Mathlib.MeasureTheory.Measure.FiniteMomentStieltjes

/-!
# Atomic moment sums at reciprocal zeros

Analytic zero isolation makes the carrying set of the logarithmic-derivative
moment measure countable. Its transform is therefore the convergent sum of
the actual singleton masses, indexed without choosing an enumeration.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate NNReal

namespace RealRooted

/-- The zero slope together with the slopes reciprocal to the real zeros of a
nonzero entire function form a countable set. -/
theorem countable_zero_or_reciprocal_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) :
    {x : ℝ≥0 | x = 0 ∨ f ((-(x : ℝ)⁻¹ : ℝ) : ℂ) = 0}.Countable := by
  have hne : f ≠ 0 := fun h ↦ hf0 (congrFun h 0)
  have hi : Function.Injective (fun x : ℝ≥0 ↦ ((-(x : ℝ)⁻¹ : ℝ) : ℂ)) := by
    intro x y h
    exact NNReal.coe_injective
      (inv_injective (neg_injective (Complex.ofReal_injective h)))
  have hs := (hf.countable_zeroSet hne).preimage hi
  convert hs.insert 0 using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_preimage]

/-- The logarithmic derivative is the convergent atomic moment sum, with all
positive masses subsequently identified by
`measureReal_singleton_eq_mul_order_of_logDeriv_integral`.
The origin is included and contributes the constant exponential coefficient. -/
theorem hasSum_logDeriv_singleton_masses
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu)
    {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    HasSum (fun a : ℝ≥0 ↦ (mu.real {a} : ℂ) / (1 + z * ((a : ℝ) : ℂ)))
      (logDeriv f z) := by
  have hslit : z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz))
  have hs := hasSum_integral_of_ae_mem_countable_ambient
    (countable_zero_or_reciprocal_zero hf hf0)
    (ae_zero_or_reciprocal_zero_of_logDeriv_integral hf hc mu hlog)
    (mu.integrable_inv_one_add_mul_of_mem_slitPlane hslit)
  rw [← hlog z hz] at hs
  simpa only [Complex.real_smul, div_eq_mul_inv] using hs

end RealRooted
