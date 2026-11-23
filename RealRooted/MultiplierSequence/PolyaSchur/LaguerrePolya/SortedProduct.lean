module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.CStarAlgebra.Classes
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MomentTypeI
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.MomentResidues
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.SortedMomentAtoms
import RealRooted.Mathlib.MeasureTheory.Measure.SortedAtomicSequence

/-!
# Sorted distinct-root products and their moment measures

The actual reciprocal-root product is reindexed along a strictly decreasing
sequence of positive slopes. Finite and empty zero sets use extra slopes of
multiplicity zero. The same sequence gives the entire product and the exact
moment measure, with the genuine product limit recorded at every complex point.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate NNReal

namespace RealRooted

/-- An injective positive family covering all nontrivial reciprocal-root factors
preserves the genuine product limit. Additional zero-multiplicity slopes are allowed. -/
theorem hasProd_pow_order_comp_of_logDeriv_integral {ι : Type*}
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hne : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z ≠ 0)
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu)
    {a : ι → ℝ≥0} (hi : Function.Injective a) (ha : ∀ i, a i ≠ 0)
    (hcover : {x : ℝ≥0 | x ≠ 0 ∧
      analyticOrderNatAt f ((-(x : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0} ⊆ range a) (z : ℂ) :
    HasProd (fun i ↦ (1 + ((a i : ℝ) : ℂ) * z) ^
      analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ))
      (f z / (f 0 * exp ((mu.real {0} : ℂ) * z))) := by
  let g : ι → {x : ℝ≥0 // x ≠ 0} := fun i ↦ ⟨a i, ha i⟩
  have hgi : Function.Injective g := fun i j h ↦ hi (congrArg Subtype.val h)
  have hout (x : {x : ℝ≥0 // x ≠ 0}) (hx : x ∉ range g) :
      (1 + ((x : ℝ) : ℂ) * z) ^ analyticOrderNatAt f ((-(x : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    have hm : analyticOrderNatAt f ((-(x : ℝ)⁻¹ : ℝ) : ℂ) = 0 := by
      by_contra hm
      obtain ⟨i, hi⟩ := hcover ⟨x.property, hm⟩
      exact hx ⟨i, Subtype.ext hi⟩
    rw [hm, pow_zero]
  exact (hgi.hasProd_iff hout).mpr
    (hasProd_pow_order_of_logDeriv_integral hf hf0 hc mu hne hlog z)

/-- A finite moment transform for an entire logarithmic derivative gives a
single sorted sequence representing both the exact measure and the entire
function. Multiplicities are actual analytic orders; zero padding covers finite
and empty root sets. No growth bound is assumed. -/
theorem exists_strictAnti_logDeriv_factorization
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hne : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z ≠ 0)
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) :
    ∃ a : ℕ → ℝ≥0, StrictAnti a ∧ (∀ i, 0 < a i) ∧
      Summable (fun i ↦ (a i : ℝ)) ∧
      Summable (fun i ↦ (a i : ℝ) *
        (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) ∧
      mu = mu {0} • Measure.dirac 0 + Measure.sum (fun i ↦ ENNReal.ofReal
        ((a i : ℝ) * (analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) •
          Measure.dirac (a i)) ∧
      ∀ z : ℂ, HasProd (fun i ↦ (1 + ((a i : ℝ) : ℂ) * z) ^
          analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ))
          (f z / (f 0 * exp ((mu.real {0} : ℂ) * z))) ∧
        f z = f 0 * exp ((mu.real {0} : ℂ) * z) * ∏' i,
          (1 + ((a i : ℝ) : ℂ) * z) ^ analyticOrderNatAt f ((-(a i : ℝ)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨a, ha, hpos, hs, hms, hmu, hcover⟩ :=
    mu.exists_strictAnti_atomic_representation
      (fun x ↦ analyticOrderNatAt f ((-(x : ℝ)⁻¹ : ℝ) : ℂ))
      (fun x hx ↦ measureReal_singleton_eq_mul_order_of_logDeriv_integral hf hf0 mu hlog hx)
      (ae_zero_or_order_ne_zero_of_logDeriv_integral hf hf0 hc mu hlog)
  refine ⟨a, ha, hpos, hs, hms, hmu, fun z ↦ ?_⟩
  have hp := hasProd_pow_order_comp_of_logDeriv_integral hf hf0 hc mu hne hlog
    ha.injective (fun i ↦ (hpos i).ne') hcover z
  refine ⟨hp, ?_⟩
  have heq := (eq_div_iff (mul_ne_zero hf0 (exp_ne_zero _))).mp hp.tprod_eq
  simpa only [mul_comm] using heq.symm

end RealRooted
