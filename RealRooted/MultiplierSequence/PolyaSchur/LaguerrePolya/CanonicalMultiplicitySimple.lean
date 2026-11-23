module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Topology.Algebra.InfiniteSum.Real
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalDifferentialSimple
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GenusOneSplit
import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GaussianProductBound

/-!
# Canonical differential simplicity with explicit multiplicities

Natural multiplicities are expanded into individual factors, then the
sparse-factor argument is applied. Zero multiplicities and zero slopes
contribute no zeros; finite and empty products cannot satisfy the infinite
zero hypothesis unless the scalar prefactor vanishes.
-/

public section

open Complex

namespace RealRooted

/-- Multiplicity-weighted real canonical symbols with infinitely many
distinct zeros have simple nonzero differential images at the sharp
Gaussian threshold. -/
theorem IsLaguerrePolya.canonical_multiplicity_differential_simple_or_zero
    {φ f : ℂ → ℂ} (hf : IsLaguerrePolya f) {ι : Type*}
    (a : ι → ℝ) (m : ι → ℕ)
    (hm : Summable (fun i ↦ (m i : ℝ) * a i ^ 2)) (c b : ℝ) (k : ℕ) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : 4 * α * β < 1)
    (heq : ∀ z, φ z = (c : ℂ) * z ^ k * exp (-(α : ℂ) * z ^ 2 + (b : ℂ) * z) *
      ∏' i, weierstrassFactor 1 ((a i : ℂ) * z) ^ m i)
    (hinf : Set.Infinite {x : ℝ | φ x = 0})
    (hfbound : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖f z‖ ≤ C * Real.exp ((β + ε) * ‖z‖ ^ 2)) :
    infiniteDifferentialApply φ f = 0 ∨
      IsLaguerrePolya (infiniteDifferentialApply φ f) ∧
      ∀ z, infiniteDifferentialApply φ f z = 0 →
        z.im = 0 ∧ _root_.deriv (infiniteDifferentialApply φ f) z ≠ 0 := by
  have hs : Summable (fun j : Σ i, Fin (m i) ↦ a j.1 ^ 2) :=
    (TauCeti.summable_sigma_fin_iff (fun i ↦ sq_nonneg (a i)) m).mpr hm
  have hsC : Summable (fun i ↦ (m i : ℝ) * ‖(a i : ℂ)‖ ^ 2) := by
    simpa only [norm_real, Real.norm_eq_abs, sq_abs] using hm
  apply hf.canonical_differential_simple_or_zero
    (fun j : Σ i, Fin (m i) ↦ a j.1) hs c b k hα hβ hab _ hinf hfbound
  intro z
  rw [heq z, tprod_weierstrassFactor_one_pow_eq_fin_copies
    (fun i ↦ (a i : ℂ)) m hsC z]

/-- The literal canonical-product form of Cardon--de Gaston (2005),
Theorem 1: actual infinite-zero symbols give zero or simple LP output when
the two Gaussian coefficients have product below one quarter. -/
theorem IsLaguerrePolya.canonical_product_differential_simple_or_zero
    {φ f : ℂ → ℂ} (hf : IsLaguerrePolya f) {ι κ : Type*}
    (a : ι → ℝ) (m : ι → ℕ) (u : κ → ℂ) (v : κ → ℕ)
    (hm : Summable (fun i ↦ (m i : ℝ) * a i ^ 2))
    (hv : Summable (fun i ↦ (v i : ℝ) * ‖u i‖ ^ 2))
    (c b : ℝ) (cf bf : ℂ) (k kf : ℕ) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : 4 * α * β < 1)
    (hφeq : ∀ z, φ z = (c : ℂ) * z ^ k * exp (-(α : ℂ) * z ^ 2 + (b : ℂ) * z) *
      ∏' i, weierstrassFactor 1 ((a i : ℂ) * z) ^ m i)
    (hfeq : ∀ z, f z = cf * z ^ kf * exp (-(β : ℂ) * z ^ 2 + bf * z) *
      ∏' i, weierstrassFactor 1 (u i * z) ^ v i)
    (hinf : Set.Infinite {x : ℝ | φ x = 0}) :
    infiniteDifferentialApply φ f = 0 ∨
      IsLaguerrePolya (infiniteDifferentialApply φ f) ∧
      ∀ z, infiniteDifferentialApply φ f z = 0 →
        z.im = 0 ∧ _root_.deriv (infiniteDifferentialApply φ f) z ≠ 0 := by
  apply hf.canonical_multiplicity_differential_simple_or_zero
    a m hm c b k hα hβ hab hφeq hinf
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := exists_norm_canonicalProduct_le_exp_sq u v hv cf bf kf hβ hε
  exact ⟨C, hC, fun z ↦ by simpa only [hfeq z] using hbound z⟩

end RealRooted
