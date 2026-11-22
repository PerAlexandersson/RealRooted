module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen
public import Mathlib.Analysis.Calculus.DSlope
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Removing real factors from Laguerre–Pólya functions

Division by an actual real zero preserves the Laguerre–Pólya class, without
any order-of-growth restriction. The proof removes the corresponding factor
from each Jensen polynomial, rather than assuming a canonical product.
-/

public section

open Polynomial Complex
open scoped ComplexConjugate

namespace RealRooted

/-- Conjugation symmetry descends through multiplication by the variable. -/
private theorem conj_of_id_mul {g : ℂ → ℂ} (hg : Continuous g)
    (hconj : ∀ z, conj z * g (conj z) = conj (z * g z)) :
    ∀ z, g (conj z) = conj (g z) := by
  have heq : (fun z => g (conj z)) = fun z => conj (g z) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      (hg.comp continuous_conj) (continuous_conj.comp hg)
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hc := hconj z
    rw [map_mul] at hc
    have hcz : conj z ≠ 0 := by simpa using hz0
    exact mul_left_cancel₀ hcz hc
  exact fun z => congrFun heq z

/-- The Jensen polynomial of `z g(z)` is a scalar times `X` times the
preceding-degree Jensen polynomial of `g`. -/
theorem jensenPolynomial_id_mul {g : ℂ → ℂ} (hg : Differentiable ℂ g) (d : ℕ) :
    jensenPolynomial (d + 1) (fun k => (iteratedDeriv k (fun z => z * g z) 0).re) =
      C (d + 1 : ℝ) * (X * jensenPolynomial d (fun k => (iteratedDeriv k g 0).re)) := by
  have hder (k : ℕ) :
      iteratedDeriv (k + 1) (fun z => z * g z) 0 = (k + 1 : ℂ) * iteratedDeriv k g 0 := by
    rw [iteratedDeriv_fun_mul (by fun_prop) hg.contDiff.contDiffAt]
    simp [iteratedDeriv_fun_id_zero, mul_ite, ite_mul]
  ext k
  cases k with
  | zero => simp
  | succ k =>
      simp only [coeff_jensenPolynomial, coeff_C_mul, coeff_X_mul, hder]
      by_cases hk : k ≤ d
      · rw [ite_eq_left (by lia), ite_eq_left hk]
        have hchoose : ((d + 1).choose (k + 1) : ℝ) * (k + 1) =
            (d + 1 : ℝ) * (d.choose k : ℝ) := by
          exact_mod_cast (Nat.add_one_mul_choose_eq d k).symm
        simp only [mul_re, add_re, natCast_re, one_re, add_im, natCast_im, one_im,
          add_zero, zero_mul, sub_zero]
        linear_combination (iteratedDeriv k g 0).re * hchoose
      · rw [ite_eq_right (by lia), ite_eq_right hk, mul_zero]

/-- Removing a variable factor from an entire LP function preserves the class. -/
theorem IsLaguerrePolya.of_id_mul {g : ℂ → ℂ}
    (h : IsLaguerrePolya (fun z => z * g z)) (hg : Differentiable ℂ g) :
    IsLaguerrePolya g := by
  have hconj := conj_of_id_mul hg.continuous h.conj
  apply (isLaguerrePolya_iff_jensenPolynomial_splits hg
    (fun k => (ofReal_re_iteratedDeriv_zero hconj k).symm)).mpr
  intro d
  have hs := h.jensenPolynomial_splits (d + 1)
  rw [jensenPolynomial_id_mul hg] at hs
  have hc : (C (d + 1 : ℝ) : ℝ[X]) ≠ 0 := C_ne_zero.mpr (by positivity)
  exact splits_X_mul.mp ((splits_mul_iff_right hc (Splits.C _)).mp hs)

/-- Removing any real linear factor from an entire LP function preserves the class. -/
theorem IsLaguerrePolya.of_sub_mul {g : ℂ → ℂ} (r : ℝ)
    (h : IsLaguerrePolya (fun z => (z - r) * g z)) (hg : Differentiable ℂ g) :
    IsLaguerrePolya g := by
  have hs : IsLaguerrePolya (fun z => z * g (z + r)) := by
    simpa using h.comp_affine_real 1 r
  have hdiv := hs.of_id_mul (hg.comp (by fun_prop))
  simpa using hdiv.comp_affine_real 1 (-r)

/-- Any power of a real linear factor can be removed from an entire LP function. -/
theorem IsLaguerrePolya.of_sub_pow_mul {g : ℂ → ℂ} (r : ℝ) (m : ℕ)
    (h : IsLaguerrePolya (fun z => (z - r) ^ m * g z)) (hg : Differentiable ℂ g) :
    IsLaguerrePolya g := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      have hs : IsLaguerrePolya (fun z => (z - r) * ((z - r) ^ m * g z)) := by
        convert h using 1
        funext z
        ring
      exact ih (hs.of_sub_mul r (by fun_prop))

/-- Dividing by an actual real zero, with the removable value filled by the
derivative, preserves LP without any growth hypothesis. -/
theorem IsLaguerrePolya.dslope_of_eq_zero {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    {r : ℝ} (hr : f r = 0) : IsLaguerrePolya (dslope f (r : ℂ)) := by
  have hd : Differentiable ℂ (dslope f (r : ℂ)) :=
    differentiableOn_univ.mp ((differentiableOn_dslope (by simp)).mpr
      hf.differentiable.differentiableOn)
  apply IsLaguerrePolya.of_sub_mul r _ hd
  convert hf using 1
  funext z
  simpa only [smul_eq_mul] using sub_smul_dslope_of_zero hr z

end RealRooted
