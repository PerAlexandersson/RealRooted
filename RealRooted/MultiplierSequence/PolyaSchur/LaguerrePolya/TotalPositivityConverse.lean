module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TotalPositivity
import RealRooted.EdreiThoma.Converse
import RealRooted.AissenSchoenbergWhitney
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Entire Pólya-frequency generating functions

An entire function whose ordinary Taylor coefficients form a Pólya-frequency
sequence belongs to the positive Type-I Laguerre--Pólya class, provided its
constant coefficient is positive. The Edrei representation has no denominator
factors: a positive denominator parameter would give a positive real pole,
whereas the numerator is nonzero there.

This is the positive-constant case of Theorem C in O. M. Katkova,
*Multiple positivity and the Riemann zeta-function*, arXiv:math/0505174.
The Taylor coefficients must be real; taking only their real parts does not
suffice for the converse.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- An entire identity with an Edrei numerator excludes positive denominator parameters. -/
private theorem eq_zero_of_mul_prod_sub_eq_exp_mul_prod
    {f : ℂ → ℂ} {γ : ℝ} {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (sα : Summable α)
    (h : ∀ z, f z * (∏' i, (1 - (β i : ℂ) * z)) =
      Complex.exp (γ * z) * ∏' i, (1 + (α i : ℂ) * z)) :
    ∀ i, β i = 0 := by
  intro i
  by_contra hi
  let r : ℝ := (β i)⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr (hβ i)
  have hB : (∏' j, (1 - (β j : ℂ) * (r : ℂ))) = 0 := by
    apply tprod_of_exists_eq_zero
    refine ⟨i, ?_⟩
    simp [r, hi]
  have hA : (∏' j, (1 + (α j : ℂ) * (r : ℂ))) ≠ 0 := by
    apply tprod_one_add_ne_zero_of_summable
    · intro j
      have : 0 < 1 + α j * r := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (hα j) hr)
      exact_mod_cast this.ne'
    · simpa only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
        abs_of_nonneg (hα _)] using sα.mul_right r
  have hz := h (r : ℂ)
  rw [hB, mul_zero] at hz
  exact (mul_ne_zero (Complex.exp_ne_zero _) hA) hz.symm

/-- The normalized Edrei germ of an entire function extends to a Type-I product. -/
private theorem exists_eq_exp_mul_prod_of_normalized
    {a : ℕ → ℝ} {f : ℂ → ℂ} (ha : IsPolyaFreqSeq a) (ha0 : a 0 = 1)
    (hf : Differentiable ℂ f)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (a n : ℂ) * z ^ n) (f z)) :
    ∃ (γ : ℝ) (α : ℕ → ℝ), 0 ≤ γ ∧ (∀ i, 0 ≤ α i) ∧ Summable α ∧
      f = fun z => Complex.exp (γ * z) * ∏' i, (1 + (α i : ℂ) * z) := by
  obtain ⟨γ, α, β, hγ, hα, hβ, sα, sβ, hrep⟩ :=
    EdreiThoma.exists_hasSum_edreiFunction ha ha0
  let E : ℂ → ℂ := fun z => Complex.exp (γ * z) * ∏' i, (1 + (α i : ℂ) * z)
  let B : ℂ → ℂ := fun z => ∏' i, (1 - (β i : ℂ) * z)
  have hE : IsLaguerrePolya E := by
    simpa [E] using
      (isLaguerrePolyaTypeI_product zero_le_one 0 hγ hα sα).toLaguerrePolya
  have hB : Differentiable ℂ B := by
    have hplus : IsLaguerrePolya (fun z : ℂ => ∏' i, (1 + (β i : ℂ) * z)) := by
      simpa using
        (isLaguerrePolyaTypeI_product zero_le_one 0 (σ := 0) le_rfl hβ sβ).toLaguerrePolya
    simpa [B, Function.comp_def, sub_eq_add_neg] using
      hplus.differentiable.comp differentiable_neg
  have hB0 : B 0 ≠ 0 := by simp [B]
  have hBne : ∀ᶠ z in 𝓝 (0 : ℂ), B z ≠ 0 :=
    hB.continuous.continuousAt.eventually_ne hB0
  have hev : (fun z => f z * B z) =ᶠ[𝓝 0] E := by
    filter_upwards [hs, hrep, hBne] with z hs hz hBz
    have heq : f z = E z / B z := by
      simpa [Complex.EdreiThoma.edreiFunction, E, B] using hs.unique hz
    exact (eq_div_iff hBz).mp heq
  have hid : (fun z => f z * B z) = E :=
    ((hf.mul hB).differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      hE.analyticOnNhd hev
  have hβ0 : ∀ i, β i = 0 :=
    eq_zero_of_mul_prod_sub_eq_exp_mul_prod hα hβ sα (congrFun hid)
  refine ⟨γ, α, hγ, hα, sα, ?_⟩
  simpa [B, E, hβ0] using hid

/-- An entire function with a real PF generating-series germ and positive constant
coefficient is Type-I Laguerre--Pólya. -/
theorem IsPolyaFreqSeq.isLaguerrePolyaTypeI_of_hasSum
    {a : ℕ → ℝ} {f : ℂ → ℂ} (ha : IsPolyaFreqSeq a) (ha0 : 0 < a 0)
    (hf : Differentiable ℂ f)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (a n : ℂ) * z ^ n) (f z)) :
    IsLaguerrePolyaTypeI f := by
  let b : ℕ → ℝ := fun n => (a 0)⁻¹ * a n
  let g : ℂ → ℂ := fun z => (a 0 : ℂ)⁻¹ * f z
  have hb : IsPolyaFreqSeq b := ha.const_mul_sequence _ (inv_nonneg.mpr ha0.le)
  have hb0 : b 0 = 1 := by simp [b, ha0.ne']
  have hg : Differentiable ℂ g := hf.const_mul _
  have hgs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (b n : ℂ) * z ^ n) (g z) := by
    filter_upwards [hs] with z hz
    simpa [b, g, mul_assoc] using hz.mul_left (a 0 : ℂ)⁻¹
  obtain ⟨γ, α, hγ, hα, sα, heq⟩ := exists_eq_exp_mul_prod_of_normalized hb hb0 hg hgs
  have heqf : f = fun z => (a 0 : ℂ) * z ^ 0 * Complex.exp (γ * z) *
      ∏' i, (1 + (α i : ℂ) * z) := by
    funext z
    have h := congrFun heq z
    have h0 : (a 0 : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    simpa [g, h0, mul_assoc] using congrArg (fun w : ℂ => (a 0 : ℂ) * w) h
  rw [heqf]
  exact isLaguerrePolyaTypeI_product ha0.le 0 hγ hα sα

/-- For an entire function with real Taylor data and positive constant coefficient,
Type-I Laguerre--Pólya membership is equivalent to total positivity of the ordinary
Taylor coefficient sequence. -/
theorem isLaguerrePolyaTypeI_iff_isPolyaFreqSeq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ k, iteratedDeriv k f 0 = ((iteratedDeriv k f 0).re : ℂ))
    (h0 : 0 < (f 0).re) :
    IsLaguerrePolyaTypeI f ↔
      IsPolyaFreqSeq (fun k => (iteratedDeriv k f 0).re / k.factorial) := by
  refine ⟨IsLaguerrePolyaTypeI.isPolyaFreqSeq, fun h => ?_⟩
  apply h.isLaguerrePolyaTypeI_of_hasSum (by simpa using h0) hf
  apply Eventually.of_forall
  intro z
  convert hasSum_taylorSeries_of_entire hf 0 z using 1
  funext k
  rw [hreal k]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm]

end RealRooted
