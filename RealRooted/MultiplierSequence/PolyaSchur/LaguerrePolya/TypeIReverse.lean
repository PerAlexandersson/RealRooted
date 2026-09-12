import RealRooted.MultiplierSequence.PolyaSchur.Factorial
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.PolyaSchur.Limit

/-!
# Reverse Type-I Pólya--Schur bridge

This file recovers a PF multiplier sequence from the Taylor data of a Type-I
Laguerre--Pólya function.  It also identifies those Taylor data with the
coefficients of the exponential generating function whenever that defining
power series has positive radius.

The positive-radius hypothesis is essential for the raw `tsum`-based
definition of `complexExpGeneratingFunction`: outside its convergence disc,
a nonsummable series is assigned the value zero.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

private theorem tendstoLocallyUniformly_iterate_deriv_eval_map
    {p : ℕ → ℝ[X]} {f : ℂ → ℂ}
    (hlim : TendstoLocallyUniformly
      (fun n (z : ℂ) => ((p n).map Complex.ofRealHom).eval z) f atTop)
    (k : ℕ) :
    TendstoLocallyUniformly
      (fun n (z : ℂ) => (((Polynomial.derivative^[k]) (p n)).map
        Complex.ofRealHom).eval z)
      ((deriv^[k]) f) atTop := by
  induction k with
  | zero => simpa using hlim
  | succ k ih =>
      have hderiv := (tendstoLocallyUniformlyOn_univ.mpr ih).deriv
        (Eventually.of_forall fun n =>
          (Polynomial.differentiable
            (((Polynomial.derivative^[k]) (p n)).map Complex.ofRealHom)).differentiableOn)
        isOpen_univ
      rw [tendstoLocallyUniformlyOn_univ] at hderiv
      convert hderiv using 1
      · ext n z
        simp only [Function.comp_apply, Polynomial.deriv, Function.iterate_succ_apply',
          Polynomial.derivative_map]
      · rw [Function.iterate_succ_apply']

private theorem eval_zero_map_iterate_derivative
    (p : ℝ[X]) (k : ℕ) :
    (((Polynomial.derivative^[k]) p).map Complex.ofRealHom).eval 0 =
      (((k.factorial : ℝ) * p.coeff k : ℝ) : ℂ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
    Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul,
    Complex.ofRealHom_eq_coe]

/-- Taylor data at zero of a Type-I Laguerre--Pólya function form a PF
multiplier sequence. -/
theorem IsLaguerrePolyaTypeI.isPFMultiplierSequence_of_iteratedDeriv_zero
    {f : ℂ → ℂ} {gamma : ℕ → ℝ} (hf : IsLaguerrePolyaTypeI f)
    (htaylor : ∀ k, (deriv^[k]) f 0 = (gamma k : ℂ)) :
    IsPFMultiplierSequence gamma := by
  rcases hf with ⟨p, hp, hlim⟩
  apply isPFMultiplierSequence_of_tendsto
    (gamma := fun n k => (k.factorial : ℝ) * (p n).coeff k)
  · exact fun n => (hp n).isPFMultiplierSequence_factorial_mul_coeff
  · intro k
    have hcomplex :=
      (tendstoLocallyUniformly_iterate_deriv_eval_map hlim k).tendstoLocallyUniformlyOn.tendsto_at
        (Set.mem_univ (0 : ℂ))
    have hreal := (Complex.continuous_re.tendsto _).comp hcomplex
    convert hreal using 1
    · funext n
      rw [Function.comp_apply, eval_zero_map_iterate_derivative]
      simp
    · rw [htaylor k]
      simp

private theorem iteratedDeriv_complexExpGeneratingFunction_zero
    (gamma : ℕ → ℝ) {R : NNReal} (hR : 0 < R)
    (hsum : Summable (fun k => ‖gamma k‖ * (R : ℝ) ^ k / k.factorial)) (k : ℕ) :
    (deriv^[k]) (complexExpGeneratingFunction gamma) 0 = (gamma k : ℂ) := by
  let c : ℕ → ℂ := fun n => ((gamma n / n.factorial : ℝ) : ℂ)
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ c
  have hsum' : Summable (fun n => ‖p n‖ * (R : ℝ) ^ n) := by
    dsimp only [p]
    simp_rw [FormalMultilinearSeries.ofScalars_norm ℂ c]
    convert hsum using 1
    ext n
    simp only [Complex.norm_real, c, norm_div, Real.norm_natCast]
    ring
  have hle : (R : ENNReal) ≤ p.radius := p.le_radius_of_summable_norm hsum'
  have hp : 0 < p.radius := (ENNReal.coe_pos.mpr hR).trans_le hle
  have hfact := (p.hasFPowerSeriesOnBall hp).factorial_smul 1 k
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow,
    one_mul] at hfact
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hfact
  rw [show complexExpGeneratingFunction gamma = p.sum by
    rfl]
  rw [← iteratedDeriv_eq_iterate, ← hfact]
  simp only [p, FormalMultilinearSeries.coeff_ofScalars, c]
  push_cast
  field_simp [Nat.factorial_ne_zero]

/-- If an exponential generating series has positive radius and its sum is
Type-I Laguerre--Pólya, then its coefficients form a PF multiplier sequence. -/
theorem IsLaguerrePolyaTypeI.isPFMultiplierSequence_of_eq_complexExpGeneratingFunction
    {f : ℂ → ℂ} {gamma : ℕ → ℝ} (hf : IsLaguerrePolyaTypeI f)
    (hfgamma : f = complexExpGeneratingFunction gamma)
    (hpositive : ∃ R : NNReal, 0 < R ∧
      Summable (fun k => ‖gamma k‖ * (R : ℝ) ^ k / k.factorial)) :
    IsPFMultiplierSequence gamma := by
  rcases hpositive with ⟨R, hR, hsum⟩
  apply hf.isPFMultiplierSequence_of_iteratedDeriv_zero
  intro k
  rw [hfgamma]
  exact iteratedDeriv_complexExpGeneratingFunction_zero gamma hR hsum k

/-- Pólya--Schur classification for an exponential generating series with a
positive radius of convergence. -/
theorem isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction
    {gamma : ℕ → ℝ}
    (hpositive : ∃ R : NNReal, 0 < R ∧
      Summable (fun k => ‖gamma k‖ * (R : ℝ) ^ k / k.factorial)) :
    IsPFMultiplierSequence gamma ↔
      IsLaguerrePolyaTypeI (complexExpGeneratingFunction gamma) := by
  constructor
  · exact IsPFMultiplierSequence.isLaguerrePolyaTypeI_complexExpGeneratingFunction
  · intro htypeI
    exact htypeI.isPFMultiplierSequence_of_eq_complexExpGeneratingFunction rfl hpositive

end RealRooted
