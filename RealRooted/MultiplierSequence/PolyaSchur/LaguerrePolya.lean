import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.PolyaSchur.Analytic
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Laguerre--Pólya limits of Jensen polynomials

This analytic leaf defines the zero-aware Laguerre--Pólya class as locally
uniform limits of real-coefficient splitting polynomials. It proves the
forward bridge from an infinite multiplier sequence to its complex
exponential-generating function under the explicit all-radius summability
majorant, together with closure of this class under products. It does not
prove an analytic root-closure theorem or either Pólya--Schur classification
direction.
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

/-- The zero function belongs to the zero-aware Laguerre--Pólya class. -/
@[simp]
theorem IsLaguerrePolya.zero : IsLaguerrePolya 0 := by
  refine ⟨fun _ => 0, fun _ => Or.inl rfl, ?_⟩
  intro u hu x
  refine ⟨Set.univ, univ_mem, ?_⟩
  filter_upwards [] with n y
  intro _
  simpa using (refl_mem_uniformity hu : ((0 : ℂ), 0) ∈ u)

/-- A Laguerre--Pólya limit of real-coefficient polynomials commutes with
complex conjugation. -/
theorem IsLaguerrePolya.conj {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (z : ℂ) :
    f (star z) = star (f z) := by
  rcases hf with ⟨p, hp, hptend⟩
  have hleft : Tendsto (fun n => ((p n).map Complex.ofRealHom).eval (star z)) atTop
      (𝓝 (f (star z))) :=
    hptend.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ _)
  have hright : Tendsto (fun n => star (((p n).map Complex.ofRealHom).eval z)) atTop
      (𝓝 (star (f z))) :=
    continuous_star.tendsto (f z) |>.comp
      (hptend.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ _))
  apply tendsto_nhds_unique hleft
  convert hright using 1
  ext n
  have hmap : Complex.ofRealHom = algebraMap ℝ ℂ := by
    ext x
    rfl
  rw [hmap, Polynomial.eval_map, Polynomial.eval_map]
  simpa only [Polynomial.aeval_def, starRingEnd_apply] using (aeval_conj (p n) z)

/-- The zero-aware Laguerre--Pólya class is closed under products. -/
theorem IsLaguerrePolya.mul {f g : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (hg : IsLaguerrePolya g) :
    IsLaguerrePolya (f * g) := by
  rcases hf with ⟨p, hp, hptend⟩
  rcases hg with ⟨q, hq, hqtend⟩
  refine ⟨fun n => p n * q n, ?_, ?_⟩
  · intro n
    rcases hp n with hpzero | hpsplit
    · simp [hpzero]
    rcases hq n with hqzero | hqsplit
    · simp [hqzero]
    · exact Or.inr (hpsplit.mul hqsplit)
  · let hmul := hptend.mul₀ hqtend
        (hptend.continuous <| Filter.Frequently.of_forall fun n =>
          Polynomial.continuous ((p n).map Complex.ofRealHom))
        (hqtend.continuous <| Filter.Frequently.of_forall fun n =>
          Polynomial.continuous ((q n).map Complex.ofRealHom))
    convert hmul using 1
    · ext n z
      simp only [Pi.mul_apply, Polynomial.map_mul, Polynomial.eval_mul]

/-- Precomposition by a real affine map preserves the zero-aware
Laguerre--Pólya class. -/
theorem IsLaguerrePolya.comp_affine_real {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (a b : ℝ) :
    IsLaguerrePolya (fun z => f ((a : ℂ) * z + b)) := by
  rcases hf with ⟨p, hp, hptend⟩
  refine ⟨fun n => (p n).comp (C a * X + C b), ?_, ?_⟩
  · intro n
    rcases hp n with hpzero | hpsplit
    · simp [hpzero]
    · right
      apply hpsplit.comp_of_natDegree_le_one
      exact (natDegree_add_le _ _).trans <|
        max_le (by simpa using natDegree_C_mul_X_pow_le a 1) (by simp)
  · have hcomp := hptend.comp (fun z : ℂ => (a : ℂ) * z + b)
      ((continuous_const.mul continuous_id).add continuous_const)
    convert hcomp using 1
    · ext n z
      simp only [Function.comp_apply, Polynomial.map_comp, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      change ((p n).map Complex.ofRealHom).eval ((a : ℂ) * z + b) =
        ((p n).map Complex.ofRealHom).eval ((a : ℂ) * z + b)
      rfl
    · ext z
      rfl

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
