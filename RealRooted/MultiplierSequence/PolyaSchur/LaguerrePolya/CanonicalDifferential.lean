module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialGaussianType
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GaussianProductBound

/-!
# Infinite differential preservation from literal canonical products

This supplies the canonical-factor form of the convergence and preservation
input in Cardon--de Gaston (2005), Lemma 2, including vanishing Gaussian
coefficients, arbitrary origin orders, and zero functions. It is not the
infinite-zero strictness conclusion of their Theorem 1.
-/

public section

open Complex

namespace RealRooted

/-- Literal genus-one canonical representations with Gaussian coefficient
product below one quarter give LP preservation of the actual infinite
differential image. Natural multiplicities and origin factors are explicit. -/
theorem IsLaguerrePolya.infiniteDifferentialApply_of_canonical
    {φ f : ℂ → ℂ} (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f)
    {ι κ : Type*} (a : ι → ℂ) (m : ι → ℕ) (u : κ → ℂ) (v : κ → ℕ)
    (hm : Summable (fun i => (m i : ℝ) * ‖a i‖ ^ 2))
    (hv : Summable (fun i => (v i : ℝ) * ‖u i‖ ^ 2))
    (cφ bφ cf bf : ℂ) (kφ kf : ℕ) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : 4 * α * β < 1)
    (hφeq : ∀ z, φ z = cφ * z ^ kφ * exp (-(α : ℂ) * z ^ 2 + bφ * z) *
      ∏' i, weierstrassFactor 1 (a i * z) ^ m i)
    (hfeq : ∀ z, f z = cf * z ^ kf * exp (-(β : ℂ) * z ^ 2 + bf * z) *
      ∏' i, weierstrassFactor 1 (u i * z) ^ v i) :
    IsLaguerrePolya (infiniteDifferentialApply φ f) := by
  apply hφ.infiniteDifferentialApply_of_gaussian_type hf hα hβ hab
  · intro ε hε
    obtain ⟨C, hC, hbound⟩ := exists_norm_canonicalProduct_le_exp_sq a m hm cφ bφ kφ hα hε
    exact ⟨C, hC, fun z => by simpa only [hφeq z] using hbound z⟩
  · intro ε hε
    obtain ⟨C, hC, hbound⟩ := exists_norm_canonicalProduct_le_exp_sq u v hv cf bf kf hβ hε
    exact ⟨C, hC, fun z => by simpa only [hfeq z] using hbound z⟩

end RealRooted
