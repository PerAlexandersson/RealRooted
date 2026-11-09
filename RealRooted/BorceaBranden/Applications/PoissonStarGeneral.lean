module

public import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Taylor
import RealRooted.DerivativeProduct.KernelWeyl

/-!
# General-factor consequences for the univariate Poisson product

This file specializes the finite-order Weyl-symbol preserver theorem to the
univariate Poisson product.  It proves real-rootedness preservation from the
root-sign condition and derives the PF-preserver classification for every real parameter
(`preservesPF_iff`): PF left factors for `c ≥ 0`, nonnegative constants for `c < 0` (issue #1494).
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted.Poisson

noncomputable section

private theorem C_pow_mul_hasseDeriv_eq (c : ℝ) (j : ℕ) (f : ℝ[X]) :
    C ((c : ℂ) ^ j) * X ^ j * hasseDeriv j (complexify f) =
      complexify
        (C (c ^ j / (j.factorial : ℝ)) * X ^ j *
          (derivative^[j]) f) := by
  have hfactorial : (j.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hhasse := congrFun (factorial_smul_hasseDeriv (R := ℂ) j)
    (complexify f)
  change (j.factorial : ℕ) • hasseDeriv j (complexify f) =
    (derivative^[j]) (complexify f) at hhasse
  rw [nsmul_eq_mul] at hhasse
  change _ = Polynomial.map Complex.ofRealHom
    (C (c ^ j / (j.factorial : ℝ)) * X ^ j * (derivative^[j]) f)
  simp only [Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  change _ = C (Complex.ofReal (c ^ j / (j.factorial : ℝ))) * X ^ j *
    complexify ((derivative^[j]) f)
  rw [complexify_iterate_derivative]
  have hhasse' :
      C (j.factorial : ℂ) * hasseDeriv j (complexify f) =
        (derivative^[j]) (complexify f) := by
    exact hhasse
  rw [← hhasse']
  have hscalar :
      (c : ℂ) ^ j =
        Complex.ofReal (c ^ j / (j.factorial : ℝ)) * (j.factorial : ℂ) := by
    norm_cast
    field_simp
  rw [hscalar, map_mul]
  ring

private theorem sum_hasseDeriv_scale (p : ℂ[X]) (c x y : ℂ) :
    (∑ j ∈ Finset.range (p.natDegree + 1),
        c ^ j * x ^ j * (hasseDeriv j p).eval x * (-1) ^ j * y ^ j) =
      p.eval (x * (1 - c * y)) := by
  calc
    (∑ j ∈ Finset.range (p.natDegree + 1),
        c ^ j * x ^ j * (hasseDeriv j p).eval x * (-1) ^ j * y ^ j) =
        (taylor x p).eval (-c * x * y) := by
          rw [Polynomial.eval_eq_sum_range, natDegree_taylor]
          apply Finset.sum_congr rfl
          intro j hj
          rw [taylor_coeff]
          simp only [mul_pow]
          ring
    _ = p.eval ((-c * x * y) + x) := by
      exact Polynomial.taylor_eval x p (-c * x * y)
    _ = p.eval (x * (1 - c * y)) := by
      congr 1
      ring

private theorem sum_eval_poisson_symbol (c : ℝ) (f : ℝ[X]) (x y : ℂ) :
    ∑ j : Fin (f.natDegree + 1),
        (complexify (C (c ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) * X ^ (j : ℕ) *
          (derivative^[j]) f)).eval x * (-y) ^ (j : ℕ) =
      (complexify f).eval (x * (1 - (c : ℂ) * y)) := by
  have hdegree : (complexify f).natDegree = f.natDegree := by
    unfold complexify
    exact Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective f
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    (complexify (C (c ^ j / (j.factorial : ℝ)) * X ^ j * (derivative^[j]) f)).eval x *
      (-y) ^ j) (f.natDegree + 1), ← sum_hasseDeriv_scale (complexify f) (c : ℂ) x y, hdegree]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← C_pow_mul_hasseDeriv_eq]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- An admissible fixed left factor sends every nonzero split polynomial to
a split polynomial or zero under the Poisson product. -/
theorem IsAdmissible.preservesRealRootedOrZero {c : ℝ} {f : ℝ[X]}
    (hf : IsAdmissible c f) :
    PreservesRealRootedOrZero (starCLinearMap c f) := by
  intro g hg
  have hsym : ∀ x y : ℂ, 0 < x.im → 0 < y.im →
      ∑ j : Fin (f.natDegree + 1),
        (complexify (C (c ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) * X ^ (j : ℕ) *
          (derivative^[j]) f)).eval x * (-y) ^ (j : ℕ) ≠ 0 := by
    intro x y hx hy
    rw [sum_eval_poisson_symbol]
    have hstable := hf.poissonSignedSymbol_stable ![x, y] (by
      intro i
      fin_cases i
      · exact hx
      · exact hy)
    rwa [eval_poissonSignedSymbol] at hstable
  have hout := sum_mul_iterate_derivative_eq_zero_or_splits (m := f.natDegree)
    (fun j ↦ C (c ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) * X ^ (j : ℕ) * (derivative^[j]) f)
    hsym hg.1 hg.2
  have hsum : ∑ j : Fin (f.natDegree + 1),
      C (c ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) * X ^ (j : ℕ) * (derivative^[j]) f *
        (derivative^[j]) g = starC c f g := by
    rw [starC]
    exact Fin.sum_univ_eq_sum_range (fun j ↦ C (c ^ j / (j.factorial : ℝ)) * X ^ j *
      (derivative^[j]) f * (derivative^[j]) g) (f.natDegree + 1)
  rw [hsum] at hout
  simpa only [starCLinearMap_apply] using hout

/-- For a nonnegative parameter, every PF polynomial is an admissible fixed
left factor. -/
theorem IsPFPolynomial.isAdmissible {c : ℝ} (hc : 0 ≤ c) {f : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) :
    IsAdmissible c f := by
  refine ⟨hf0, (hf.ne_zero_and_splits hf0).2, ?_⟩
  intro r hr
  exact mul_nonpos_of_nonneg_of_nonpos hc (hf.roots_nonpos r hr)

/-- For a nonnegative parameter, fixed Poisson multiplication by any PF
polynomial preserves the finite PF cone. -/
theorem IsPFPolynomial.preservesPF {c : ℝ} (hc : 0 ≤ c) {f : ℝ[X]}
    (hf : IsPFPolynomial f) : PreservesPF c f := by
  intro g hg
  by_cases hf0 : f = 0
  · rw [hf0, starC_zero_left]
    exact IsPFPolynomial.zero
  by_cases hg0 : g = 0
  · rw [hg0, starC_zero_right]
    exact IsPFPolynomial.zero
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact starC_nonneg hc hf.hasNonnegCoeffs hg.hasNonnegCoeffs
  · have hout :=
      (IsPFPolynomial.isAdmissible hc hf hf0).preservesRealRootedOrZero
        g (hg.ne_zero_and_splits hg0)
    simpa only [starCLinearMap_apply] using hout

/-- For a nonnegative parameter, a fixed left factor preserves all PF
polynomials exactly when it is itself PF. -/
theorem preservesPF_iff_of_nonneg {c : ℝ} (hc : 0 ≤ c) (f : ℝ[X]) :
    PreservesPF c f ↔ IsPFPolynomial f := by
  constructor
  · exact isPFPolynomial_of_preservesPF
  · intro hf
    exact IsPFPolynomial.preservesPF hc hf

/-- Complete fixed-left-factor PF classification for every real parameter. -/
theorem preservesPF_iff (c : ℝ) (f : ℝ[X]) :
    PreservesPF c f ↔
      if 0 ≤ c then IsPFPolynomial f
      else ∃ a : ℝ, 0 ≤ a ∧ f = C a := by
  split
  next hc =>
    exact preservesPF_iff_of_nonneg hc f
  next hc =>
    exact preservesPF_of_neg_iff (lt_of_not_ge hc) f

end

end RealRooted.Poisson
