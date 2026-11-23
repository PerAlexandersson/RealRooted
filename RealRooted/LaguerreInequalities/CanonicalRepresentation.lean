module

public import RealRooted.LaguerreInequalities.CanonicalProduct
import RealRooted.LaguerreInequalities.CanonicalLogDerivative
import RealRooted.LaguerreInequalities.RealZeros
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Identity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.LogDeriv

/-!
# Canonical representation from generalized Laguerre inequalities

At a nonzero origin value, all generalized Laguerre inequalities reconstruct the
entire function as its actual real-zero genus-one product times a real Gaussian
exponential. In particular, they imply membership in the Laguerre--Pólya class
without an order or genus hypothesis.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- All generalized Laguerre inequalities give the real genus-one canonical
representation, with a nonnegative Gaussian coefficient, when zero is not a root. -/
theorem exists_eq_exp_mul_realZeroProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    ∃ a b : ℝ, 0 ≤ b ∧ ∀ z : ℂ,
      f z = f 0 * exp ((a : ℂ) * z - (b : ℂ) * z ^ 2 / 2) * realZeroProduct f z := by
  obtain ⟨a, b, hb, hlog⟩ := exists_logDeriv_eq_realZeroProduct hf hc hf0 h
  have hP := differentiable_realZeroProduct hf hc hf0 h
  let g : ℂ → ℂ := fun z => exp ((a : ℂ) * z - (b : ℂ) * z ^ 2 / 2) *
    realZeroProduct f z
  have hg : Differentiable ℂ g := by
    exact (Differentiable.cexp (by fun_prop)).mul hP
  have hgn (z : ℂ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) : g z ≠ 0 :=
    mul_ne_zero (exp_ne_zero _) (realZeroProduct_ne_zero_of_im_pos hf hc hf0 h hz)
  have hfn (z : ℂ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) : f z ≠ 0 := by
    intro hzero
    have him := im_eq_zero_of_laguerreCoefficient_nonneg hf hc
      (fun heq => hf0 (congrFun heq 0)) h hzero
    exact (ne_of_gt hz) him
  have hglog (z : ℂ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
      logDeriv g z = (a : ℂ) - (b : ℂ) * z + logDeriv (realZeroProduct f) z := by
    rw [show g = _ from rfl, TauCeti.logDeriv_cexp_mul
      (realZeroProduct_ne_zero_of_im_pos hf hc hf0 h hz) (hP z) (by fun_prop)]
    congr 1
    rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_div_const,
      deriv_const_mul_id, deriv_const_mul _ (by fun_prop), deriv_pow_field]
    norm_num
    ring
  have heq := hf.eq_mul_of_logDeriv_eqOn hg UpperHalfPlane.isOpen_upperHalfPlaneSet
    (convex_halfSpace_im_gt 0).isPreconnected ⟨I, by simp⟩ hfn hgn
    (fun z hz => (hlog z hz).trans (hglog z hz).symm)
    (by simp [g])
  exact ⟨a, b, hb, fun z => by simpa only [g, ← mul_assoc] using heq z⟩

/-- At a nonzero origin value, all generalized Laguerre inequalities imply
membership in the Laguerre--Pólya class without a growth assumption. -/
theorem isLaguerrePolya_of_laguerreCoefficient_nonneg_of_ne_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hf0 : f 0 ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) : IsLaguerrePolya f := by
  obtain ⟨a, b, hb, heq⟩ := exists_eq_exp_mul_realZeroProduct hf hc hf0 h
  have hzero : ((f 0).re : ℂ) = f 0 := by
    apply conj_eq_iff_re.mp
    simpa using (hc 0).symm
  have hlin : IsLaguerrePolya (fun z : ℂ => exp ((a : ℂ) * z)) := by
    simpa using isLaguerrePolya_exp.comp_affine_real a 0
  have hgauss := isLaguerrePolya_exp_neg_mul_sq (div_nonneg hb (by norm_num : (0 : ℝ) ≤ 2))
  have hp := ((hlin.mul hgauss).const_mul_real (f 0).re).mul
    (isLaguerrePolya_realZeroProduct hf hc hf0 h)
  convert hp using 1
  funext z
  rw [heq z]
  simp only [Pi.mul_apply, hzero, ← exp_add, ofReal_div, ofReal_ofNat]
  congr 3
  ring

end RealRooted
