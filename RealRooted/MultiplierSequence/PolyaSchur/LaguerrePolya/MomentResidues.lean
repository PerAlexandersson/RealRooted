module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
import RealRooted.Mathlib.MeasureTheory.Measure.MomentNevanlinnaRepresentation
public import Mathlib.Analysis.Analytic.Order
import RealRooted.Mathlib.MeasureTheory.Measure.AtomicRange
import RealRooted.LaguerreInequalities.AtomMultiplicity
import RealRooted.LaguerreInequalities.MeasureSupport
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.NormalizedConjugation

/-!
# Integer residues of logarithmic-derivative moment transforms

The explicit finite Nevanlinna measure identifies every positive slope atom
with the zero multiplicity at its negative reciprocal. For a real entire
function, the original moment measure is carried by these reciprocal zeros
and the origin. These steps use neither a growth bound nor a product formula.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate NNReal ENNReal

namespace RealRooted

/-- An explicit moment transform supplies finite Nevanlinna data with no linear
term. This is the representation consumed by the existing residue theorem. -/
private theorem neg_logDeriv_eq_momentNevanlinna
    {f : ℂ → ℂ} (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) :
    ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      -logDeriv f z = (0 : ℂ) * z +
        (∫ r : ℝ, TauCeti.nevanlinnaKernel z r ∂mu.momentNevanlinna) +
        ((-(∫ x : ℝ≥0, (1 + (x : ℝ) ^ 2)⁻¹ ∂mu : ℝ)) : ℂ) := by
  intro z hz
  rw [hlog z hz, mu.neg_integral_inv_one_add_mul_eq_nevanlinna hz]
  simp only [zero_mul, zero_add, sub_eq_add_neg]

/-- Every positive atom of a logarithmic-derivative moment measure is its slope
times the actual natural zero multiplicity at the negative reciprocal root. -/
theorem measureReal_singleton_eq_mul_order_of_logDeriv_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu)
    {a : ℝ≥0} (ha : a ≠ 0) :
    mu.real {a} = (a : ℝ) *
      (analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) : ℝ) := by
  have : IsFiniteMeasure mu.momentNevanlinna := mu.isFiniteMeasure_momentNevanlinna
  have hne : f ≠ 0 := fun h ↦ hf0 (congrFun h 0)
  have heq := measureReal_singleton_eq_analyticOrderNatAt_div hf hne
    (ρ := mu.momentNevanlinna) (b := 0)
    (c := -(∫ x : ℝ≥0, (1 + (x : ℝ) ^ 2)⁻¹ ∂mu : ℝ))
    (by simpa only [Complex.ofReal_zero, Complex.ofReal_neg] using
      neg_logDeriv_eq_momentNevanlinna mu hlog) (-(a : ℝ)⁻¹)
  rw [mu.momentNevanlinna_real_singleton] at heq
  have haR : (a : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr ha
  have haP : 0 < (a : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
  apply mul_left_cancel₀ (by positivity : (a : ℝ) / (1 + (a : ℝ) ^ 2) ≠ 0)
  calc
    _ = (analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) : ℝ) /
        (1 + (-(a : ℝ)⁻¹) ^ 2) := heq
    _ = _ := by
      field_simp [haR, show 1 + (a : ℝ) ^ 2 ≠ 0 by positivity]
      ring

/-- The reciprocal slopes, counted with the entire function's actual zero
multiplicities, are summable. This follows from the finite original measure,
without a genus or growth assumption. -/
theorem summable_mul_order_of_logDeriv_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) :
    Summable (fun a : {x : ℝ≥0 // x ≠ 0} ↦ (a : ℝ) *
      (analyticOrderNatAt f ((-(a : ℝ)⁻¹ : ℝ) : ℂ) : ℝ)) := by
  have hs : Summable (fun a : {x : ℝ≥0 // x ≠ 0} ↦ mu.real {(a : ℝ≥0)}) :=
    mu.summable_measureReal_singleton_comp Subtype.coe_injective
  exact hs.congr fun a ↦
    measureReal_singleton_eq_mul_order_of_logDeriv_integral hf hf0 mu hlog a.property

/-- A real entire logarithmic-derivative moment measure has no non-atomic part
away from zero: almost every positive slope is the negative reciprocal of a zero. -/
theorem ae_zero_or_reciprocal_zero_of_logDeriv_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z))
    (mu : Measure ℝ≥0) [IsFiniteMeasure mu]
    (hlog : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      logDeriv f z = ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) :
    ∀ᵐ x : ℝ≥0 ∂mu, x = 0 ∨ f ((-(x : ℝ)⁻¹ : ℝ) : ℂ) = 0 := by
  have : IsFiniteMeasure mu.momentNevanlinna := mu.isFiniteMeasure_momentNevanlinna
  have hs := support_nevanlinna_neg_logDeriv_subset_zeros hf hc
    (ρ := mu.momentNevanlinna) (b := 0)
    (c := -(∫ x : ℝ≥0, (1 + (x : ℝ) ^ 2)⁻¹ ∂mu : ℝ))
    (by simpa only [Complex.ofReal_zero, Complex.ofReal_neg] using
      neg_logDeriv_eq_momentNevanlinna mu hlog)
  have hρ : ∀ᵐ r : ℝ ∂mu.momentNevanlinna, f (r : ℂ) = 0 :=
    Filter.mem_of_superset mu.momentNevanlinna.support_mem_ae hs
  change ∀ᵐ r : ℝ ∂((mu.withDensity fun x ↦ (Measure.momentNevanlinnaWeight x : ℝ≥0∞)).map
    (fun x : ℝ≥0 ↦ -(x : ℝ)⁻¹)), f (r : ℂ) = 0 at hρ
  have hw := ae_of_ae_map (f := fun x : ℝ≥0 ↦ -(x : ℝ)⁻¹) (by fun_prop) hρ
  have hμ := (ae_withDensity_iff
    (f := fun x : ℝ≥0 ↦ (Measure.momentNevanlinnaWeight x : ℝ≥0∞)) (by fun_prop)).mp hw
  filter_upwards [hμ] with x hx
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · apply Or.inr
    apply hx
    apply ne_of_gt
    apply ENNReal.coe_pos.mpr
    change 0 < x / (1 + x ^ 2)
    exact div_pos (pos_iff_ne_zero.mpr hx0) (by positivity)

/-- A normalized entire function with a nonnegative moment transform for its
logarithmic derivative respects conjugation. The input nonvanishing and transform
identity are supplied by the local-moment continuation theorem. -/
theorem conj_of_logDeriv_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 = 1)
    (mu : Measure ℝ≥0)
    (hne : ∀ z ∈ slitPlane, f z ≠ 0)
    (hlog : EqOn (logDeriv f)
      (fun z ↦ ∫ x : ℝ≥0, (1 + z * ((x : ℝ) : ℂ))⁻¹ ∂mu) slitPlane) :
    ∀ z, f (conj z) = conj (f z) := by
  apply hf.conj_of_eqOn_logDeriv_conj hf0 hne
  intro z hz
  have hzc : conj z ∈ slitPlane := by
    simpa only [mem_slitPlane_iff, conj_re, conj_im, neg_ne_zero] using hz
  simp only [Function.comp_apply]
  rw [hlog hzc, hlog hz, ← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [map_inv₀, map_add, map_one, map_mul, conj_conj, conj_ofReal]

end RealRooted
