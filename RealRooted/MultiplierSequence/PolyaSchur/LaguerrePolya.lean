import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.PolyaSchur.Analytic

/-!
# Laguerre--Pólya limits of Jensen polynomials

This analytic leaf defines the zero-aware Laguerre--Pólya class as locally
uniform limits of real-coefficient splitting polynomials. It proves the
forward bridge from an infinite multiplier sequence to its complex
exponential-generating function under the explicit all-radius summability
majorant. It does not prove an analytic root-closure theorem or either
Pólya--Schur classification direction.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- A complex function is Laguerre--Pólya when it is a locally uniform limit
of real-coefficient polynomials that are zero or split over the reals. -/
def IsLaguerrePolya (f : ℂ → ℂ) : Prop :=
  ∃ p : ℕ → ℝ[X],
    (∀ n, p n = 0 ∨ (p n).Splits) ∧
      TendstoLocallyUniformly
        (fun n (z : ℂ) => (p n).map Complex.ofRealHom |>.eval z) f atTop

/-- The rescaled Jensen polynomial of an infinite multiplier sequence is
zero or splits over the reals. -/
theorem IsMultiplierSequence.rescaledJensenPolynomial_eq_zero_or_splits
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma) (n : ℕ) :
    rescaledJensenPolynomial n gamma = 0 ∨ (rescaledJensenPolynomial n gamma).Splits := by
  have hj : jensenPolynomial n gamma = 0 ∨ (jensenPolynomial n gamma).Splits := by
    have h := hgamma.finite n (natDegree_X_add_one_pow_le n) (splits_X_add_one_pow n)
    rwa [← jensenPolynomial_eq_diagonalOperator_X_add_one_pow] at h
  rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
  rcases hj with hzero | hsplit
  · simp [hzero]
  · right
    apply hsplit.comp_of_natDegree_le_one
    simpa using natDegree_C_mul_X_pow_le ((n : ℝ)⁻¹) 1

/-- An infinite multiplier sequence whose exponential-generating coefficients
have an all-radius summable majorant has a Laguerre--Pólya complex EGF. -/
theorem IsMultiplierSequence.isLaguerrePolya_complexExpGeneratingFunction
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hsum : ∀ R : ℝ, 0 ≤ R →
      Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    IsLaguerrePolya (complexExpGeneratingFunction gamma) := by
  refine ⟨fun n => rescaledJensenPolynomial n gamma,
    fun n => hgamma.rescaledJensenPolynomial_eq_zero_or_splits n, ?_⟩
  exact tendstoLocallyUniformly_complexExpGeneratingFunction_of_summable gamma hsum

end RealRooted
