module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.LaguerreInequalities.AuxiliaryProduct
public import Mathlib.Algebra.Polynomial.Expand
import RealRooted.LaguerreInequalities.PowerGenerating
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import RealRooted.PFPolynomial.Closure

/-!
# Total positivity for higher-even auxiliary coefficients

For the auxiliary `X^n + 1`, where `n` is positive and even, the coefficient
sequence indexed by multiples of `n` is PF for every Laguerre--Pólya function
at each real center. This is a derived strengthening of the coefficient
inequalities in Cardon's Example 2. It does not assert PF for the merely even
subsequence when `n > 2`.
-/

public section

open Complex Filter Polynomial Topology

namespace RealRooted

/-- Higher-even auxiliary products are locally uniform limits of power
substitutions of PF polynomials. -/
theorem IsLaguerrePolya.exists_pf_auxiliaryProduct_approx {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ) :
    ∃ p : ℕ → ℝ[X], (∀ i, IsPFPolynomial (p i)) ∧
      TendstoLocallyUniformly
        (fun i z ↦ ((expand ℝ n (p i)).map ofRealHom).eval z)
        (auxiliaryProduct (X ^ n + 1) f x) atTop := by
  have hc := hf.differentiable.continuous
  obtain ⟨p, hp, hlim⟩ := hf
  have hs (i : ℕ) : (p i).Splits := (hp i).elim (fun h ↦ h ▸ Splits.zero) id
  have hprod := tendstoLocallyUniformly_auxiliaryProduct hlim hc (X ^ n + 1) x
  refine ⟨fun i ↦ powerGeneratingPolynomial n (p i) x,
    fun i ↦ isPFPolynomial_powerGeneratingPolynomial he (p i) x, ?_⟩
  convert hprod using 1
  ext i z
  simp only [expand_eq_comp_X_pow, Polynomial.map_comp, Polynomial.map_pow, map_X,
    eval_comp, eval_pow, eval_X, eval_powerGeneratingPolynomial_pow hn (hs i)]

/-- These are actual real Taylor coefficients, not merely bounds on the
real parts of possibly nonreal coefficients. -/
theorem IsLaguerrePolya.auxiliaryCoefficient_ofReal {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ) (k : ℕ) :
    iteratedDeriv k (auxiliaryProduct (X ^ n + 1) f x) 0 / k.factorial =
      (auxiliaryCoefficient (X ^ n + 1) f x k : ℂ) := by
  obtain ⟨p, _, hlim⟩ := hf.exists_pf_auxiliaryProduct_approx hn he x
  have hreal := Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim k
  have hcomplex := Polynomial.tendsto_coeff_ofReal_of_tendstoLocallyUniformly hlim k
  have hcast := (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [Function.comp_def, Complex.div_natCast_re, auxiliaryCoefficient] using
    tendsto_nhds_unique hcomplex hcast

/-- The higher-even auxiliary product has no coefficients outside the
multiples of its auxiliary degree. -/
theorem IsLaguerrePolya.auxiliaryCoefficient_eq_zero {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ)
    {k : ℕ} (hk : ¬n ∣ k) : auxiliaryCoefficient (X ^ n + 1) f x k = 0 := by
  obtain ⟨p, _, hlim⟩ := hf.exists_pf_auxiliaryProduct_approx hn he x
  have hc := Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim k
  have hz : (fun i ↦ (expand ℝ n (p i)).coeff k) = (fun _ : ℕ ↦ (0 : ℝ)) := by
    funext i
    simp only [coeff_expand (Nat.pos_of_ne_zero hn), ite_eq_right hk]
  rw [hz] at hc
  simpa only [Complex.div_natCast_re, auxiliaryCoefficient] using
    tendsto_nhds_unique hc tendsto_const_nhds

/-- The coefficients with index divisible by the even auxiliary degree are
coefficientwise limits of PF polynomials. -/
theorem IsLaguerrePolya.exists_pf_auxiliaryCoefficient_approx {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ) :
    ∃ p : ℕ → ℝ[X], (∀ i, IsPFPolynomial (p i)) ∧
      ∀ k, Tendsto (fun i ↦ (p i).coeff k) atTop
        (𝓝 (auxiliaryCoefficient (X ^ n + 1) f x (n * k))) := by
  obtain ⟨p, hp, hlim⟩ := hf.exists_pf_auxiliaryProduct_approx hn he x
  refine ⟨p, hp, fun k ↦ ?_⟩
  simpa only [coeff_expand_mul' (Nat.pos_of_ne_zero hn), Complex.div_natCast_re,
    auxiliaryCoefficient] using
    Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim (n * k)

/-- The compressed higher-even auxiliary coefficient sequence is PF at
all real centers. This includes functions vanishing at the center. -/
theorem IsLaguerrePolya.isPolyaFreqSeq_auxiliaryCoefficient {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ) :
    IsPolyaFreqSeq (fun k ↦ auxiliaryCoefficient (X ^ n + 1) f x (n * k)) := by
  obtain ⟨p, hp, hlim⟩ := hf.exists_pf_auxiliaryCoefficient_approx hn he x
  exact IsPolyaFreqSeq.of_tendsto (fun i ↦ (hp i).to_sequence) hlim

/-- Every Taylor coefficient of a positive-even auxiliary product is
nonnegative, including indices not divisible by the auxiliary degree. -/
theorem IsLaguerrePolya.auxiliaryCoefficient_power_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ) (k : ℕ) :
    0 ≤ auxiliaryCoefficient (X ^ n + 1) f x k := by
  obtain ⟨p, hp, hlim⟩ := hf.exists_pf_auxiliaryProduct_approx hn he x
  have hc := Polynomial.tendsto_coeff_of_tendstoLocallyUniformly hlim k
  have hbound (i : ℕ) : 0 ≤ (expand ℝ n (p i)).coeff k := by
    rw [coeff_expand (Nat.pos_of_ne_zero hn)]
    split_ifs
    · exact (hp i).hasNonnegCoeffs _
    · exact le_rfl
  simpa only [Complex.div_natCast_re, auxiliaryCoefficient] using
    ge_of_tendsto hc (Eventually.of_forall hbound)

end RealRooted
