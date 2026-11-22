module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.BorceaBranden.Transcendental.UniformSzasz
import RealRooted.Mathlib.Analysis.Complex.Polynomial.CoeffEstimates
import RealRooted.HermiteBiehler.Basic
import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Entire convergence from formal Jensen hyperbolicity

If all Jensen polynomials of a real sequence split, its exponential generating
series converges everywhere and belongs to the Laguerre--Pólya class. No prior
analytic convergence assumption is needed. The proof uses the Szász bound on
rescaled Jensen polynomials, including sequences with an arbitrary zero prefix.
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

private theorem summable_of_jensenPolynomial_splits (gamma : ℕ → ℝ)
    (h : ∀ n, (jensenPolynomial n gamma).Splits) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial) := by
  let p : ℕ → ℝ[X] := fun n => rescaledJensenPolynomial n gamma
  have hp (n : ℕ) : (p n).Splits := by
    dsimp [p]
    rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
    exact (h n).comp_of_natDegree_le_one ((natDegree_C_mul_le _ _).trans (by simp))
  let f : ℕ → MvPolynomial Unit ℂ := fun n =>
    (MvPolynomial.uniqueAlgEquiv ℂ Unit).symm ((p n).map ofRealHom)
  let a : (Unit →₀ ℕ) → ℂ := fun e => (gamma (e ()) / (e ()).factorial : ℝ)
  let κ : ℕ → (Unit →₀ ℕ) → ℝ := fun n e =>
    (n.choose (e ()) : ℝ) * ((n : ℝ)⁻¹) ^ e () * (e ()).factorial
  have hcoef (n : ℕ) (e : Unit →₀ ℕ) : (f n).coeff e = (κ n e : ℂ) * a e := by
    simp only [f, MvPolynomial.coeff_uniqueAlgEquiv_symm, coeff_map, p,
      coeff_rescaledJensenPolynomial, κ, a]
    by_cases he : e () ≤ n
    · rw [ite_eq_left he]
      simp only [ofRealHom_eq_coe]
      push_cast
      have hfac : (((e ()).factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (e ())
      field_simp [hfac]
    · rw [ite_eq_right he, Nat.choose_eq_zero_of_lt (lt_of_not_ge he)]
      simp
  have hκ (e : Unit →₀ ℕ) : Tendsto (fun n => κ n e) atTop (𝓝 1) := by
    have ht := (Nat.tendsto_choose_mul_inv_pow_atTop (e ())).mul_const
      ((e ()).factorial : ℝ)
    simpa [κ, div_eq_mul_inv, Nat.factorial_ne_zero] using ht
  have hst (n : ℕ) : MvUpperHalfPlaneStable (f n) ∨ f n = 0 := by
    by_cases hn : p n = 0
    · right
      simp [f, hn]
    · left
      intro z hz
      change MvPolynomial.eval₂ (RingHom.id ℂ) z (f n) ≠ 0
      rw [show f n = (MvPolynomial.uniqueAlgEquiv ℂ Unit).symm
        ((p n).map ofRealHom) from rfl]
      rw [MvPolynomial.eval₂_uniqueAlgEquiv_symm]
      exact isUpperHalfPlaneStable_complexify_of_splits (hp n) hn (z ()) (hz ())
  obtain ⟨B, C, n₀, hbound⟩ :=
    BorceaBranden.exists_norm_eval_le_exp_sq a κ f hcoef hκ hst
  have hlimit (e : Unit →₀ ℕ) :
      Tendsto (fun n => (f (n + n₀)).coeff e) atTop (𝓝 (a e)) := by
    simp only [hcoef]
    have ht := ((hκ e).comp (tendsto_add_atTop_nat n₀)).ofReal.mul_const (a e)
    simpa using ht
  obtain ⟨hsum, _⟩ := MvPolynomial.tendstoLocallyUniformly_of_bounded_of_coeff_tendsto
    (fun n => f (n + n₀)) a
    (fun r hr => ⟨B * Real.exp (C * r ^ 2),
      fun n z hz => hbound (n + n₀) (Nat.le_add_left _ _) r hr.le z hz⟩) hlimit
  have hs := (hsum (fun _ : Unit => (R : ℂ))).comp_injective
    (Finsupp.single_injective ())
  simpa [a, Function.comp_def, norm_mul, norm_pow, abs_of_nonneg hR, norm_div,
    mul_div_assoc, div_mul_eq_mul_div] using hs

/-- Formal Jensen hyperbolicity forces absolute convergence of the exponential
generating series at every nonnegative radius, even with an initial zero prefix. -/
theorem summable_norm_div_factorial_of_jensenPolynomial_splits (gamma : ℕ → ℝ)
    (h : ∀ n, (jensenPolynomial n gamma).Splits) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial) :=
  summable_of_jensenPolynomial_splits gamma h R hR

/-- All real Jensen polynomials splitting already implies that the formal
exponential generating function is an entire Laguerre--Pólya function. -/
theorem isLaguerrePolya_of_jensenPolynomial_splits (gamma : ℕ → ℝ)
    (h : ∀ n, (jensenPolynomial n gamma).Splits) :
    IsLaguerrePolya (complexExpGeneratingFunction gamma) := by
  rw [complexExpGeneratingFunction_eq_tsum]
  refine ⟨fun n => rescaledJensenPolynomial n gamma, fun n => Or.inr ?_,
    tendstoLocallyUniformly_eval_complex_rescaledJensenPolynomial_of_summable gamma
      (summable_of_jensenPolynomial_splits gamma h)⟩
  dsimp only
  rw [rescaledJensenPolynomial_eq_jensenPolynomial_comp]
  exact (h n).comp_of_natDegree_le_one ((natDegree_C_mul_le _ _).trans (by simp))

end RealRooted
