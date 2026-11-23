module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.CanonicalSparseFactor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GenusZeroFactorSimple
import RealRooted.Mathlib.Analysis.Complex.LinearProductNonpolynomial
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.GaussianMargin

/-!
# Simple zeros for infinite-zero canonical differential symbols

This is the canonical-input form of Cardon--de Gaston (2005), Theorem 1.
The hypothesis concerns the actual infinitely many distinct real zeros of
the symbol, and the conclusion concerns the actual infinite differential
series. No nonzero cofactor image is assumed.
-/

public section

open Complex

namespace RealRooted

/-- A real canonical symbol with infinitely many distinct zeros gives a
zero or simple LP differential image under the strict Gaussian threshold.
Both Gaussian coefficients may vanish, and origin orders are arbitrary. -/
theorem IsLaguerrePolya.canonical_differential_simple_or_zero
    {φ f : ℂ → ℂ} (hf : IsLaguerrePolya f) {ι : Type*} (a : ι → ℝ)
    (ha : Summable (fun i ↦ a i ^ 2)) (c b : ℝ) (k : ℕ) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hab : 4 * α * β < 1)
    (heq : ∀ z, φ z = (c : ℂ) * z ^ k * exp (-(α : ℂ) * z ^ 2 + (b : ℂ) * z) *
      ∏' i, weierstrassFactor 1 ((a i : ℂ) * z))
    (hinf : Set.Infinite {x : ℝ | φ x = 0})
    (hfbound : ∀ ε > 0, ∃ C > 0, ∀ z,
      ‖f z‖ ≤ C * Real.exp ((β + ε) * ‖z‖ ^ 2)) :
    infiniteDifferentialApply φ f = 0 ∨
      IsLaguerrePolya (infiniteDifferentialApply φ f) ∧
      ∀ z, infiniteDifferentialApply φ f z = 0 →
        z.im = 0 ∧ _root_.deriv (infiniteDifferentialApply φ f) z ≠ 0 := by
  by_cases hc : c = 0
  · have hφ0 : φ = 0 := by funext z; simp [heq z, hc]
    left
    rw [hφ0]
    ext z
    simp only [infiniteDifferentialApply, iteratedDeriv_const_zero, zero_mul,
      zero_div, tsum_zero, Pi.zero_apply]
  · obtain ⟨s, g, hs, hsinj, hs0, hg, hgbound, hfactor⟩ :=
      exists_genusZero_factor_of_canonical ha hc b k hα heq hinf
    obtain ⟨A, B, hαA, hβB, hA, hB, hAB⟩ :=
      Real.exists_pos_gaussian_coefficients hα hβ hab
    obtain ⟨Mg, hMg, hgBound⟩ := hgbound (A - α) (sub_pos.mpr hαA)
    obtain ⟨Mf, hMf, hfBound⟩ := hfbound (B - β) (sub_pos.mpr hβB)
    have hgBound' : ∀ z, ‖g z‖ ≤ Mg * Real.exp (A * ‖z‖ ^ 2) := by
      have he : α + (A - α) = A := by ring
      simpa only [he] using hgBound
    have hfBound' : ∀ z, ‖f z‖ ≤ Mf * Real.exp (B * ‖z‖ ^ 2) := by
      have he : β + (B - β) = B := by ring
      simpa only [he] using hfBound
    have h := hg.genusZero_factor_differential_simple_or_zero hf hs
      (tprod_one_add_ne_polynomial_of_injective hsinj hs0)
      hMg.le hMf.le hA hB hAB hgBound' hfBound'
    have hφ : φ = fun z ↦ (∏' n, (1 + (s n : ℂ) * z)) * g z := funext hfactor
    simpa only [hφ] using h

end RealRooted
