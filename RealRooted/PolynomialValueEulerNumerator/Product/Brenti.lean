import RealRooted.PolynomialValueEulerNumerator.Product.PF

/-!
# Brenti's theorem on Euler numerators

F. Brenti, *Unimodal, log-concave and Pólya frequency sequences in combinatorics*,
Mem. Amer. Math. Soc. 81 (1989), no. 413, Theorem 4.4.4: if every zero of the real
polynomial `p` lies in `[-1, 0]` and its leading coefficient is positive, then the numerator
`W` of `∑ₙ p(n) xⁿ = W(x) / (1 - x)^(deg p + 1)` is a PF polynomial (real-rooted with
nonnegative coefficients).

For a linear factor `X + a` the numerator is `a + (1 - a) X`, which is PF exactly when
`0 ≤ a ≤ 1`; Wagner's product theorem `IsPFPolynomial.polynomialValueEulerNumerator_mul`
then handles the product over the roots.
-/

open Polynomial

noncomputable section

namespace RealRooted

@[simp]
theorem polynomialValueEulerNumerator_C (c : ℝ) :
    polynomialValueEulerNumerator (C c) = C c := by
  rw [polynomialValueEulerNumerator, natDegree_C]
  simp [finiteEulerNumerator, polynomialValueSeq]

theorem polynomialValueEulerNumerator_X_add_C (a : ℝ) :
    polynomialValueEulerNumerator (X + C a) = C a + C (1 - a) * X := by
  rw [polynomialValueEulerNumerator, natDegree_X_add_C]
  norm_num [finiteEulerNumerator, Finset.sum_range_succ,
    polynomialValueSeq, fwdDiff, Function.iterate_succ_apply']
  ring

/-- The Euler numerator `a + (1 - a) X` of `X + a` is PF for `0 ≤ a ≤ 1`. -/
theorem isPFPolynomial_polynomialValueEulerNumerator_X_add_C {a : ℝ} (h0 : 0 ≤ a)
    (h1 : a ≤ 1) : IsPFPolynomial (polynomialValueEulerNumerator (X + C a)) := by
  rw [polynomialValueEulerNumerator_X_add_C]
  refine IsPFPolynomial.of_realRooted_nonneg (fun k => ?_)
    (Splits.of_natDegree_le_one (by compute_degree!))
  rcases k with _ | _ | k <;> simp [coeff_C, coeff_X, coeff_one, h0, sub_nonneg.mpr h1]

/-- **Brenti's theorem.**  If every root of `p` lies in `[-1, 0]` and `p` has nonnegative
leading coefficient, the Euler numerator of `n ↦ p(n)` is a PF polynomial. -/
theorem IsPFPolynomial.polynomialValueEulerNumerator_of_roots_mem_Icc {p : ℝ[X]}
    (hs : p.Splits) (hlc : 0 ≤ p.leadingCoeff) (hroots : ∀ r ∈ p.roots, -1 ≤ r ∧ r ≤ 0) :
    IsPFPolynomial (polynomialValueEulerNumerator p) := by
  rw [hs.eq_prod_roots]
  generalize p.roots = s at hroots
  induction s using Multiset.induction_on with
  | empty => simpa using IsPFPolynomial.of_C_nonneg hlc
  | cons r s ih =>
    have hr := hroots r (Multiset.mem_cons_self r s)
    rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm, mul_comm]
    refine IsPFPolynomial.polynomialValueEulerNumerator_mul
      (ih fun x hx => hroots x (Multiset.mem_cons_of_mem hx)) ?_
    simpa [sub_eq_add_neg] using
      isPFPolynomial_polynomialValueEulerNumerator_X_add_C (a := -r) (by linarith)
        (by linarith)

end RealRooted
