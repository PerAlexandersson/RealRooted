module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MomentResidues
import RealRooted.Mathlib.Analysis.Complex.LinearProductAnalytic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.AtomicMomentSum
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeILinearProduct
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiniteMultiplicity
import RealRooted.Mathlib.Topology.Algebra.InfiniteSum.FiniteMultiplicityProduct
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Identity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Type-I reconstruction from a logarithmic-derivative moment transform

The finite positive measure is supported at zero and at reciprocal zeros of the
entire function. Its positive atoms are their slopes times natural zero
multiplicities. Repeating each slope accordingly produces a summable genus-zero
product. Equality of logarithmic derivatives recovers the normalized function.
No growth hypothesis is used.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate NNReal

namespace RealRooted

private abbrev ReciprocalZeroIndex (f : ℂ → ℂ) :=
  Σ a : {x : ℝ≥0 // x ≠ 0}, Fin (analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ))

private def reciprocalZeroSlope (f : ℂ → ℂ) (j : ReciprocalZeroIndex f) : ℝ :=
  (j.1 : ℝ)

/-- Repeating the actual positive reciprocal slopes by their natural zero
multiplicities gives a summable family. -/
private theorem summable_reciprocalZeroSlope
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) :
    Summable (reciprocalZeroSlope f) := by
  apply summable_sigma_fin_of_nonneg
    (fun a : {x : ℝ≥0 // x ≠ 0} ↦ analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ))
    (fun a ↦ (a : ℝ≥0).coe_nonneg)
  simpa only [mul_comm] using summable_mul_order_of_logDeriv_integral hf hf0 mu hlog

/-- Removing the zero atom from the atomic moment sum gives precisely the
logarithmic derivative of the product with the actual zero multiplicities. -/
private theorem logDeriv_eq_atom_add_reciprocal_product
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu)
    {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    logDeriv f z = (mu.real {0} : ℂ) +
      logDeriv (fun w ↦ ∏' j : ReciprocalZeroIndex f,
        (1 + (reciprocalZeroSlope f j : ℂ) * w)) z := by
  classical
  have hs := hasSum_logDeriv_singleton_masses hf hf0 hc mu hlog hz
  have hpos : HasSum (fun a : {x : ℝ≥0 // x ≠ 0} ↦
      (mu.real {(a : ℝ≥0)} : ℂ) / (1 + z * ((a : ℝ) : ℂ)))
      (logDeriv f z - (mu.real {0} : ℂ)) := by
    have hs' := (Finset.hasSum_iff_compl ({0} : Finset ℝ≥0)).mp hs
    have hp : (fun x : ℝ≥0 ↦ x ∉ ({0} : Finset ℝ≥0)) = (fun x ↦ x ≠ 0) := by
      funext x
      simp only [Finset.mem_singleton]
    rw [hp] at hs'
    simpa only [Finset.sum_singleton, NNReal.coe_zero, ofReal_zero, mul_zero,
      add_zero, div_one] using hs'
  have hgroup := HasSum.sigma_fin_const_div
    (a := fun a : {x : ℝ≥0 // x ≠ 0} ↦ (a : ℝ))
    (m := fun a ↦ analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ))
    (hasSum_logDeriv_tprod_one_add_ofReal_mul
      (summable_reciprocalZeroSlope hf hf0 mu hlog) hz)
  have hpos' : HasSum (fun a : {x : ℝ≥0 // x ≠ 0} ↦
      (analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) : ℂ) * (a : ℝ) /
        (1 + ((a : ℝ) : ℂ) * z))
      (logDeriv f z - (mu.real {0} : ℂ)) := by
    apply hpos.congr_fun
    intro a
    rw [measureReal_singleton_eq_mul_order_of_logDeriv_integral hf hf0 mu hlog a.property]
    push_cast
    ring
  have heq := hgroup.unique hpos'
  linear_combination -heq

/-- Recover the entire function from the convergent reciprocal-root product.
The same identity supplies Type-I membership and the explicit product formula. -/
private theorem eq_mul_exp_mul_reciprocal_product
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hne : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z ≠ 0)
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) (z : ℂ) :
    f z = f 0 * exp ((mu.real {0} : ℂ) * z) *
      ∏' j : ReciprocalZeroIndex f, (1 + (reciprocalZeroSlope f j : ℂ) * z) := by
  have hs := summable_reciprocalZeroSlope hf hf0 mu hlog
  let P : ℂ → ℂ := fun w ↦ ∏' j : ReciprocalZeroIndex f,
    (1 + (reciprocalZeroSlope f j : ℂ) * w)
  let E : ℂ → ℂ := fun w ↦ exp ((mu.real {0} : ℂ) * w)
  let G : ℂ → ℂ := E * P
  have hG : IsLaguerrePolyaTypeI G :=
    isLaguerrePolyaTypeI_exp_mul_tprod
      (fun j : ReciprocalZeroIndex f ↦ (j.1 : ℝ≥0).coe_nonneg) hs measureReal_nonneg
  have hP : Differentiable ℂ P := differentiable_tprod_one_add_ofReal_mul hs
  have hPn : ∀ w ∈ UpperHalfPlane.upperHalfPlaneSet, P w ≠ 0 :=
    fun _ hw ↦ tprod_one_add_ofReal_mul_ne_zero_of_im_pos hs hw
  have hElog (w : ℂ) : logDeriv E w = (mu.real {0} : ℂ) := by
    rw [logDeriv_apply, show deriv E w = _ from
      (hasDerivAt_const_mul (mu.real {0} : ℂ)).cexp.deriv]
    exact mul_div_cancel_left₀ _ (exp_ne_zero _)
  have hGlog : EqOn (logDeriv f) (logDeriv G) UpperHalfPlane.upperHalfPlaneSet := by
    intro w hw
    rw [show logDeriv G w = logDeriv E w + logDeriv P w from
      logDeriv_mul w (exp_ne_zero _) (hPn w hw) (by dsimp [E]; fun_prop) (hP w), hElog]
    exact logDeriv_eq_atom_add_reciprocal_product hf hf0 hc mu hlog hw
  have hG0 : G 0 = 1 := by simp [G, E, P, Pi.mul_apply]
  have heq := hf.eq_mul_of_logDeriv_eqOn (g := G) hG.toLaguerrePolya.differentiable
    UpperHalfPlane.isOpen_upperHalfPlaneSet (convex_halfSpace_im_gt 0).isPreconnected
    ⟨I, by simp⟩ hne (fun w hw ↦ mul_ne_zero (exp_ne_zero _) (hPn w hw)) hGlog hG0
  simpa only [G, E, P, Pi.mul_apply, mul_assoc] using heq z

/-- The reciprocal-root factors, grouped by their actual natural multiplicities,
converge to the normalized entire function after removing its exponential factor.
This is a genuine product limit, including at zeros of the function. -/
theorem hasProd_pow_order_of_logDeriv_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hne : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z ≠ 0)
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) (z : ℂ) :
    HasProd (fun a : {x : ℝ≥0 // x ≠ 0} ↦
      (1 + ((a : ℝ) : ℂ) * z) ^ analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ))
      (f z / (f 0 * exp ((mu.real {0} : ℂ) * z))) := by
  have hs := summable_reciprocalZeroSlope hf hf0 mu hlog
  have hp := HasProd.sigma_fin_const
    (a := fun a : {x : ℝ≥0 // x ≠ 0} ↦ (1 + ((a : ℝ) : ℂ) * z))
    (m := fun a ↦ analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ))
    ((hasProdLocallyUniformlyOn_one_add_ofReal_mul hs).hasProd (mem_univ z))
  rw [eq_mul_exp_mul_reciprocal_product hf hf0 hc mu hne hlog z,
    mul_div_cancel_left₀ _ (mul_ne_zero hf0 (exp_ne_zero _))]
  exact hp

/-- A normalized entire function with a finite nonnegative moment transform
for its actual logarithmic derivative is positive Type-I. The global transform
and its nonvanishing domain are supplied by local-moment continuation. -/
theorem isLaguerrePolyaTypeI_of_logDeriv_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 1)
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hne : ∀ z ∈ slitPlane, f z ≠ 0)
    (hlog : EqOn (logDeriv f)
      (fun z ↦ ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) slitPlane) :
    IsLaguerrePolyaTypeI f := by
  have hf0n : f 0 ≠ 0 := by simp only [hf0, ne_eq, one_ne_zero, not_false_eq_true]
  have hH : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, z ∈ slitPlane :=
    fun z hz ↦ mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz))
  have hlogH := fun z hz ↦ hlog (hH z hz)
  have hc := conj_of_logDeriv_integral hf hf0 mu hne hlog
  have hs := summable_reciprocalZeroSlope hf hf0n mu hlogH
  have heq := eq_mul_exp_mul_reciprocal_product hf hf0n hc mu
    (fun z hz ↦ hne z (hH z hz)) hlogH
  have hfg : f = fun z ↦ exp ((mu.real {0} : ℂ) * z) *
      ∏' j : ReciprocalZeroIndex f, (1 + (reciprocalZeroSlope f j : ℂ) * z) := by
    funext z
    simpa only [hf0, one_mul] using heq z
  rw [hfg]
  exact isLaguerrePolyaTypeI_exp_mul_tprod
    (fun j : ReciprocalZeroIndex f ↦ (j.1 : ℝ≥0).coe_nonneg) hs measureReal_nonneg

end RealRooted
