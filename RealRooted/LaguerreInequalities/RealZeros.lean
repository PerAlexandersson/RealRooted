module

public import RealRooted.LaguerreInequalities.Analytic
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Real zeros from generalized Laguerre inequalities

For a nonzero real entire function, nonnegative generalized Laguerre coefficients
at every real point force every zero to be real. The argument uses the entire
Taylor series of the product of opposite imaginary translates. It does not
require a growth assumption.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- Odd derivatives of the even Laguerre product vanish at the origin. -/
theorem iteratedDeriv_laguerreProduct_odd (f : ℂ → ℂ) (x : ℝ) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n (laguerreProduct f x) 0 = 0 := by
  have heven : (fun z => laguerreProduct f x (-z)) = laguerreProduct f x := by
    ext z
    exact laguerreProduct_neg f x z
  have h := iteratedDeriv_comp_neg n (laguerreProduct f x) 0
  rw [heven, neg_zero, hn.neg_one_pow, neg_one_smul] at h
  linear_combination h / 2

private theorem laguerre_taylor_nonneg {f : ℂ → ℂ} (x : ℝ)
    (h : ∀ n, 0 ≤ laguerreCoefficient f x n) (n : ℕ) :
    0 ≤ (iteratedDeriv n (laguerreProduct f x) 0).re / n.factorial := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, rfl⟩ := hn
    simpa only [laguerreCoefficient, two_mul] using h k
  · rw [iteratedDeriv_laguerreProduct_odd f x hn]
    simp

private theorem hasSum_laguerreProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (x y : ℝ) :
    HasSum (fun n => (iteratedDeriv n (laguerreProduct f x) 0).re / n.factorial * y ^ n)
      (laguerreProduct f x y).re := by
  have h := Complex.hasSum_re
    (Complex.hasSum_taylorSeries_of_entire (differentiable_laguerreProduct hf x) 0 (y : ℂ))
  convert h using 1
  ext n
  simp only [sub_zero, smul_eq_mul]
  rw [← Complex.div_natCast_re, ← Complex.re_mul_ofReal]
  congr 1
  push_cast
  ring

private theorem laguerreProduct_eq_zero_of_pos_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (x : ℝ)
    (h : ∀ n, 0 ≤ laguerreCoefficient f x n) {r : ℝ} (hr : 0 < r)
    (hz : laguerreProduct f x r = 0) (z : ℂ) : laguerreProduct f x z = 0 := by
  have hs := hasSum_laguerreProduct hf x r
  rw [hz, zero_re] at hs
  have hderiv (n : ℕ) : iteratedDeriv n (laguerreProduct f x) 0 = 0 := by
    have hn : 0 ≤ (iteratedDeriv n (laguerreProduct f x) 0).re / n.factorial :=
      laguerre_taylor_nonneg x h n
    have hle := le_hasSum hs n (fun j _ =>
      mul_nonneg (laguerre_taylor_nonneg x h j) (pow_nonneg hr.le j))
    have heq := le_antisymm hle (mul_nonneg hn (pow_nonneg hr.le n))
    have hcoeff := (mul_eq_zero.mp heq).resolve_right (pow_ne_zero n hr.ne')
    have hre := (div_eq_zero_iff.mp hcoeff).resolve_right
      (show (n.factorial : ℝ) ≠ 0 by positivity)
    rw [← ofReal_re_iteratedDeriv_zero (laguerreProduct_conj hc x) n, hre, ofReal_zero]
  rw [← Complex.taylorSeries_eq_of_entire' 0 z (differentiable_laguerreProduct hf x)]
  simp [hderiv]

private theorem eq_zero_of_laguerreProduct_eq_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (x : ℝ) (h : ∀ z, laguerreProduct f x z = 0) : f = 0 := by
  have hplus : Differentiable ℂ (fun z => f ((x : ℂ) + z * I)) := hf.comp (by fun_prop)
  have hminus : Differentiable ℂ (fun z => f ((x : ℂ) - z * I)) := hf.comp (by fun_prop)
  have hp : AnalyticOnNhd ℂ (fun z => f ((x : ℂ) + z * I)) Set.univ :=
    fun z _ => hplus.analyticAt z
  have hm : AnalyticOnNhd ℂ (fun z => f ((x : ℂ) - z * I)) Set.univ :=
    fun z _ => hminus.analyticAt z
  rcases hp.eq_zero_or_eq_zero_of_mul_eq_zero hm (fun z _ => h z)
    isPreconnected_univ with hp | hm
  · funext z
    change f z = 0
    have heq : (x : ℂ) + ((z - x) * (-I)) * I = z := by
      ring_nf
      simp [I_sq]
    simpa only [heq] using hp ((z - x) * (-I)) (Set.mem_univ _)
  · funext z
    change f z = 0
    have heq : (x : ℂ) - ((z - x) * I) * I = z := by
      ring_nf
      simp [I_sq]
    simpa only [heq] using hm ((z - x) * I) (Set.mem_univ _)

/-- Generalized Laguerre inequalities at all real points force all zeros of a
nonzero real entire function to be real, without a growth hypothesis. -/
theorem im_eq_zero_of_laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hne : f ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) {z : ℂ} (hz : f z = 0) : z.im = 0 := by
  by_contra him
  have hzero : laguerreProduct f z.re (z.im : ℂ) = 0 := by
    rw [laguerreProduct, re_add_im, hz, zero_mul]
  have habs : laguerreProduct f z.re (|z.im| : ℝ) = 0 := by
    rcases le_total 0 z.im with hpos | hneg
    · simpa only [abs_of_nonneg hpos] using hzero
    · simpa only [abs_of_nonpos hneg, ofReal_neg, laguerreProduct_neg] using hzero
  apply hne
  exact eq_zero_of_laguerreProduct_eq_zero hf z.re
    (laguerreProduct_eq_zero_of_pos_zero hf hc z.re (h z.re) (abs_pos.mpr him) habs)

end RealRooted
