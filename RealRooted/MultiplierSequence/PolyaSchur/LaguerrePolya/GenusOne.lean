module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.CanonicalProduct.GenusOne
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IndexedProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Star
import TauCeti.Analysis.Complex.CanonicalProduct.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.LogDeriv

/-!
# Real zeros of genus-one-star functions

A real entire function of genus `1*` is Laguerre--Pólya when all its zeros are
real. The proof starts with the complex canonical representation, recovers real
slopes from its zeros, and recovers the real constant and linear coefficients
after cancelling the origin power. No nonzero origin value is assumed.
-/

public section

open Complex Polynomial
open scoped ComplexConjugate

namespace RealRooted

private theorem im_slope_eq_zero {f : ℂ → ℂ} {c b : ℂ} {a : ℝ} {m : ℕ}
    {u : ℕ → ℂ} (hu : Summable (fun n => ‖u n‖ ^ 2))
    (heq : ∀ z, f z = c * z ^ m * exp (-(a : ℂ) * z ^ 2 + b * z) *
      ∏' n, weierstrassFactor 1 (u n * z))
    (hz : ∀ z, f z = 0 → z.im = 0) (n : ℕ) : (u n).im = 0 := by
  by_cases hn : u n = 0
  · simp [hn]
  have hr : f (u n)⁻¹ = 0 := by
    rw [heq, (tprod_weierstrassFactor_one_eq_zero_iff u hu _).mpr
      ⟨n, mul_inv_cancel₀ hn⟩, mul_zero]
  have hc := conj_eq_iff_im.mpr (hz _ hr)
  rw [map_inv₀, inv_inj] at hc
  exact conj_eq_iff_im.mp hc

private theorem real_canonical_cofactor {c b : ℂ} {a : ℝ} {u : ℕ → ℂ}
    (hc : c ≠ 0) (hu : Summable (fun n => ‖u n‖ ^ 2))
    (hconj : ∀ z, (c * (exp (-(a : ℂ) * (conj z) ^ 2 + b * conj z) *
      ∏' n, weierstrassFactor 1 (u n * conj z))) =
        conj (c * (exp (-(a : ℂ) * z ^ 2 + b * z) *
          ∏' n, weierstrassFactor 1 (u n * z)))) : c.im = 0 ∧ b.im = 0 := by
  have hcReal : c.im = 0 := by
    apply conj_eq_iff_im.mp
    simpa using (hconj 0).symm
  have hsum : Summable (fun n => ((1 : ℕ) : ℝ) * ‖u n‖ ^ 2) := by simpa using hu
  have hPlog : logDeriv (fun z => ∏' n, weierstrassFactor 1 (u n * z)) 0 = 0 := by
    have hh := logDeriv_tprod_weierstrassFactor_one_pow u (fun _ => 1) hsum
      (z := 0) (by simp)
    simpa [logDerivWeierstrassFactorOneMul_def] using hh
  have hbReal := logDeriv_ofReal_im
    (f := fun z => c * (exp (-(a : ℂ) * z ^ 2 + b * z) *
      ∏' n, weierstrassFactor 1 (u n * z))) hconj 0
  simp only [ofReal_zero] at hbReal
  rw [logDeriv_const_mul _ _ hc, TauCeti.logDeriv_cexp_mul (by simp)
    (differentiable_tprod_weierstrassFactor_one u hu 0) (by fun_prop), hPlog,
    add_zero, deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_const_mul _ (by fun_prop), deriv_pow_field, deriv_const_mul_id] at hbReal
  simpa using And.intro hcReal hbReal

/-- A real function of genus one star with only real zeros belongs to the
Laguerre--Pólya class, allowing any multiplicity at the origin. -/
theorem isLaguerrePolya_of_hasGenusOneStar {f : ℂ → ℂ}
    (hf : HasGenusOneStar f) (hc : ∀ z, f (conj z) = conj (f z))
    (hz : ∀ z, f z = 0 → z.im = 0) : IsLaguerrePolya f := by
  obtain ⟨c, b, a, m, u, hc0, ha, hu, heq⟩ := hf
  have huReal (n : ℕ) : ((u n).re : ℂ) = u n :=
    conj_eq_iff_re.mp (conj_eq_iff_im.mpr (im_slope_eq_zero hu heq hz n))
  let P : ℂ → ℂ := fun z => ∏' n, weierstrassFactor 1 (u n * z)
  have hP : IsLaguerrePolya P := by
    have hs : Summable (fun n => ((1 : ℕ) : ℝ) * (u n).re ^ 2) := by
      convert hu using 1
      funext n
      rw [Nat.cast_one, one_mul, ← huReal n]
      simp only [ofReal_re, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simpa only [pow_one, huReal] using
      isLaguerrePolya_tprod_weierstrassFactor_one_pow (fun n => (u n).re) (fun _ => 1) hs
  let g : ℂ → ℂ := fun z => c * (exp (-(a : ℂ) * z ^ 2 + b * z) * P z)
  have hg : Differentiable ℂ g := by
    exact (differentiable_const c).mul ((Differentiable.cexp (by fun_prop)).mul hP.differentiable)
  have heqf (z : ℂ) : f z = z ^ m * g z := by
    rw [heq]
    dsimp only [g, P]
    ring
  have hgc : ∀ z, g (conj z) = conj (g z) := by
    apply conj_of_pow_mul hg.continuous m
    intro z
    rw [← heqf, ← heqf, hc]
  obtain ⟨hcr, hbr⟩ := real_canonical_cofactor hc0 hu hgc
  have hcReal : (c.re : ℂ) = c := conj_eq_iff_re.mp (conj_eq_iff_im.mpr hcr)
  have hbReal : (b.re : ℂ) = b := conj_eq_iff_re.mp (conj_eq_iff_im.mpr hbr)
  have hlin : IsLaguerrePolya (fun z : ℂ => exp (b * z)) := by
    simpa only [ofReal_zero, add_zero, hbReal] using
      isLaguerrePolya_exp.comp_affine_real b.re 0
  have hid : IsLaguerrePolya (fun z : ℂ => z) := by
    simpa using isLaguerrePolya_eval_map (p := X) Splits.X
  have hresult := (((hid.pow m).mul ((isLaguerrePolya_exp_neg_mul_sq ha).mul hlin)).mul
    hP).const_mul_real c.re
  convert hresult using 1
  funext z
  rw [heq]
  simp only [Pi.mul_apply, hcReal, ← exp_add, P]
  ring

end RealRooted
