import RealRooted.MultiplierSequence.PolyaSchur.Growth

/-!
# Type-I Laguerre--Pólya limits

This leaf records the sign-sensitive Type-I sub-class of the zero-aware
Laguerre--Pólya class: its polynomial approximants are Pólya-frequency
polynomials.  It proves the forward Pólya--Schur direction for PF multiplier
sequences.  The converse classification remains separate.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- A Type-I Laguerre--Pólya function is a locally uniform limit of
Pólya-frequency polynomials.  The predicate is zero-aware because
`IsPFPolynomial` is zero-aware. -/
def IsLaguerrePolyaTypeI (f : ℂ → ℂ) : Prop :=
  ∃ p : ℕ → ℝ[X],
    (∀ n, IsPFPolynomial (p n)) ∧
      TendstoLocallyUniformly
        (fun n (z : ℂ) => (p n).map Complex.ofRealHom |>.eval z) f atTop

/-- Type-I Laguerre--Pólya functions are Laguerre--Pólya. -/
theorem IsLaguerrePolyaTypeI.toLaguerrePolya {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) :
    IsLaguerrePolya f := by
  rcases hf with ⟨p, hp, hlim⟩
  exact ⟨p, fun n => (hp n).eq_zero_or_splits, hlim⟩

private theorem IsPFMultiplierSequence.isPF_rescaledJensenPolynomial
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma) (n : ℕ) :
    IsPFPolynomial (rescaledJensenPolynomial n gamma) := by
  cases n with
  | zero =>
      simpa [rescaledJensenPolynomial] using
        IsPFPolynomial.of_C_nonneg (hgamma.nonneg 0)
  | succ n =>
      rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
      simpa using
        (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence hgamma (n + 1)).comp_C_mul_X_add_C
          (a := ((n + 1 : ℕ) : ℝ)⁻¹) (d := 0) (by positivity) (by positivity)

/-- The complex EGF of a PF multiplier sequence is Type-I
Laguerre--Pólya. -/
theorem IsPFMultiplierSequence.isLaguerrePolyaTypeI_complexExpGeneratingFunction
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma) :
    IsLaguerrePolyaTypeI (complexExpGeneratingFunction gamma) := by
  refine ⟨fun n => rescaledJensenPolynomial n gamma,
    fun n => hgamma.isPF_rescaledJensenPolynomial n, ?_⟩
  exact tendstoLocallyUniformly_complexExpGeneratingFunction_of_summable gamma
    fun R hR => hgamma.summable_expGenerating_majorant R hR

end RealRooted
