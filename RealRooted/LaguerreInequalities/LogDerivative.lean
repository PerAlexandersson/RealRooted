module

public import RealRooted.LaguerreInequalities.Analytic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import RealRooted.LaguerreInequalities.RealZeros
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The Pick property from generalized Laguerre inequalities

Nonnegative generalized Laguerre coefficients force the squared vertical modulus
to have nonnegative derivative in the upper half-plane. Consequently the negative
logarithmic derivative has nonnegative imaginary part. For a nonzero real entire
function it is holomorphic there, since the inequalities also force all zeros to
be real. No growth restriction is imposed.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- Every ordinary Taylor derivative of the Laguerre product has nonnegative real
part when all generalized Laguerre coefficients are nonnegative. Odd derivatives
vanish, and even derivatives are positive factorial multiples of those coefficients. -/
theorem iteratedDeriv_laguerreProduct_re_nonneg {f : ℂ → ℂ} (x : ℝ)
    (h : ∀ n, 0 ≤ laguerreCoefficient f x n) (n : ℕ) :
    0 ≤ (iteratedDeriv n (laguerreProduct f x) 0).re := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := hn
    have hk := h k
    rw [laguerreCoefficient, two_mul] at hk
    simpa only [zero_mul] using (le_div_iff₀ (by positivity)).mp hk
  · rw [iteratedDeriv_laguerreProduct_odd f x hn]
    simp

/-- The vertical Laguerre product has nonnegative real derivative on the
nonnegative real axis, by its entire Taylor expansion. -/
theorem re_deriv_laguerreProduct_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (x : ℝ) (h : ∀ n, 0 ≤ laguerreCoefficient f x n) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ (deriv (laguerreProduct f x) y).re := by
  have hd := (differentiable_laguerreProduct hf x).deriv
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_of_entire hd 0 (y : ℂ))
  rw [← hs.tsum_eq]
  apply tsum_nonneg
  intro n
  have hn := iteratedDeriv_laguerreProduct_re_nonneg x h (n + 1)
  rw [iteratedDeriv_succ'] at hn
  simp only [sub_zero, smul_eq_mul]
  simp only [← Complex.ofReal_natCast, ← ofReal_inv, ← ofReal_pow, mul_re,
    ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (mul_nonneg (pow_nonneg hy n) hn)

/-- The derivative of the vertical squared modulus is minus twice the imaginary
part of the derivative times the conjugate value. -/
theorem re_deriv_laguerreProduct_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (x y : ℝ) :
    (deriv (laguerreProduct f x) y).re =
      -2 * (deriv f ((x : ℂ) + y * I) * conj (f ((x : ℂ) + y * I))).im := by
  have hp : HasDerivAt (fun z : ℂ => (x : ℂ) + z * I) I (y : ℂ) := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)
  have hm : HasDerivAt (fun z : ℂ => (x : ℂ) - z * I) (-I) (y : ℂ) := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_sub (x : ℂ)
  have hd := ((hf _).hasDerivAt.comp (y : ℂ) hp).mul
    ((hf _).hasDerivAt.comp (y : ℂ) hm)
  have heq : (x : ℂ) - y * I = conj ((x : ℂ) + y * I) := by
    simp [sub_eq_add_neg]
  have hc' : deriv f (conj ((x : ℂ) + y * I)) =
      conj (deriv f ((x : ℂ) + y * I)) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_conj hc 1 ((x : ℂ) + y * I)
  rw [show deriv (laguerreProduct f x) (y : ℂ) = _ from hd.deriv]
  simp only [Function.comp_apply]
  rw [heq, hc, hc']
  simp only [add_re, mul_re, mul_im, conj_re, conj_im, I_re, I_im, neg_re, neg_im]
  ring

/-- All generalized Laguerre inequalities imply the closed Pick inequality for
the negative logarithmic derivative. This includes real-axis zeros because the
logarithmic derivative uses totalized division there. -/
theorem im_neg_logDeriv_nonneg_of_laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) {z : ℂ} (hz : 0 ≤ z.im) :
    0 ≤ (-logDeriv f z).im := by
  have hd := re_deriv_laguerreProduct_nonneg hf z.re (h z.re) hz
  rw [re_deriv_laguerreProduct_eq hf hc, re_add_im] at hd
  rw [logDeriv_apply, neg_im, div_im, ← sub_div, ← neg_div]
  apply div_nonneg _ (normSq_nonneg _)
  simp only [mul_im, conj_re, conj_im] at hd
  linarith

/-- Under the generalized Laguerre inequalities, the negative logarithmic
derivative of a real entire function is holomorphic on the upper half-plane.
For the zero function the totalized logarithmic derivative is identically zero. -/
theorem differentiableOn_neg_logDeriv_of_laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    DifferentiableOn ℂ (fun z => -logDeriv f z) UpperHalfPlane.upperHalfPlaneSet := by
  by_cases hne : f = 0
  · subst f
    simpa only [logDeriv_apply, deriv_zero, Pi.zero_apply, zero_div, neg_zero] using
      (differentiable_const (0 : ℂ)).differentiableOn
  intro z hz
  have hfz : f z ≠ 0 := by
    intro heq
    have him := im_eq_zero_of_laguerreCoefficient_nonneg hf hc hne h heq
    exact (ne_of_gt hz) him
  exact ((hf.deriv z).div (hf z) hfz).neg.differentiableWithinAt

end RealRooted
