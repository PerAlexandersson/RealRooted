import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
import RealRooted.BorceaBranden.FiniteOrderWeylPreserver
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor

/-!
# General-factor consequences for the univariate Poisson product

This file specializes the finite-order Weyl-symbol preserver theorem to the
univariate Poisson product.  It proves real-rootedness preservation from the
root-sign condition and derives the PF-preserver classification for every real parameter
(`preservesPF_iff`): PF left factors for `c ≥ 0`, nonnegative constants for `c < 0` (issue #1494).
-/

open Polynomial
open scoped BigOperators

namespace RealRooted.Poisson

noncomputable section

private def polynomialToMv (p : ℂ[X]) : MvPolynomial Unit ℂ :=
  p.eval₂ (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ) (MvPolynomial.X ())

private theorem polynomialToMv_add (p q : ℂ[X]) :
    polynomialToMv (p + q) = polynomialToMv p + polynomialToMv q := by
  simp [polynomialToMv]

private theorem polynomialToMv_mul (p q : ℂ[X]) :
    polynomialToMv (p * q) = polynomialToMv p * polynomialToMv q := by
  simp [polynomialToMv]

private theorem polynomialToMv_finset_sum {ι : Type*} (s : Finset ι)
    (p : ι → ℂ[X]) :
    polynomialToMv (∑ i ∈ s, p i) =
      ∑ i ∈ s, polynomialToMv (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialToMv]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        polynomialToMv_add, ih]

private theorem polynomialToMv_C (a : ℂ) :
    polynomialToMv (C a) = MvPolynomial.C a := by
  simp [polynomialToMv]

private theorem polynomialToMv_X :
    polynomialToMv (X : ℂ[X]) = MvPolynomial.X () := by
  simp [polynomialToMv]

private theorem pderiv_polynomialToMv (p : ℂ[X]) :
    MvPolynomial.pderiv () (polynomialToMv p) =
      polynomialToMv p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [derivative_add, polynomialToMv_add, polynomialToMv_add, map_add, hp, hq]
  | monomial n a =>
      cases n with
      | zero => simp [polynomialToMv]
      | succ n =>
          rw [show monomial (n + 1) a = C a * X ^ (n + 1) by
            simp [C_mul_X_pow_eq_monomial]]
          rw [derivative_C_mul, polynomialToMv_mul,
            polynomialToMv_C, MvPolynomial.pderiv_C_mul]
          simp [polynomialToMv]

private theorem iteratedPDerivAt_polynomialToMv (j : ℕ) (p : ℂ[X]) :
    iteratedPDerivAt () j (polynomialToMv p) =
      polynomialToMv ((derivative^[j]) p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratedPDerivAt, ih, pderiv_polynomialToMv]
      rw [Function.iterate_succ_apply']

private theorem eval_polynomialToMv (p : ℂ[X]) (z : Unit → ℂ) :
    MvPolynomial.eval z (polynomialToMv p) = p.eval (z ()) := by
  have hC :
      (MvPolynomial.eval z).comp
          (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ) = RingHom.id ℂ := by
    ext a
    simp
  simp [polynomialToMv, Polynomial.hom_eval₂, hC]

private theorem polynomialToMv_injective : Function.Injective polynomialToMv := by
  intro p q hpq
  have hleft (r : ℂ[X]) :
      MvPolynomial.eval₂ C (fun _ : Unit => X) (polynomialToMv r) = r := by
    induction r using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [polynomialToMv_add, MvPolynomial.eval₂_add, hp, hq]
    | monomial n a =>
        rw [show monomial n a = C a * X ^ n by
          simp [C_mul_X_pow_eq_monomial]]
        simp [polynomialToMv]
  have := congrArg (MvPolynomial.eval₂ C (fun _ : Unit => X)) hpq
  simpa only [hleft] using this

private theorem complexify_iterate_derivative (j : ℕ) (p : ℝ[X]) :
    complexify ((derivative^[j]) p) =
      (derivative^[j]) (complexify p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hderivative (q : ℝ[X]) :
          complexify q.derivative = (complexify q).derivative := by
        ext n
        simp [complexify, coeff_derivative]
      rw [hderivative]
      exact congrArg derivative ih

private theorem complexify_finset_sum {ι : Type*} (s : Finset ι)
    (p : ι → ℝ[X]) :
    complexify (∑ i ∈ s, p i) = ∑ i ∈ s, complexify (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexify]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change Polynomial.map Complex.ofRealHom
          (p a + ∑ i ∈ s, p i) =
        complexify (p a) + ∑ i ∈ s, complexify (p i)
      rw [Polynomial.map_add]
      change complexify (p a) + complexify (∑ i ∈ s, p i) =
        complexify (p a) + ∑ i ∈ s, complexify (p i)
      rw [ih]

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

private def poissonWeylFamily (c : ℝ) (f : ℝ[X]) :
    Fin (f.natDegree + 1) → MvPolynomial Unit ℂ := fun j =>
  polynomialToMv
    (C ((c : ℂ) ^ (j : ℕ)) * X ^ (j : ℕ) *
      hasseDeriv (j : ℕ) (complexify f))

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

private theorem eval_signedWeylSymbol_poissonWeylFamily
    (c : ℝ) (f : ℝ[X]) (z : Option Unit → ℂ) :
    MvPolynomial.eval z
        (BorceaBranden.signedWeylSymbol f.natDegree
          (poissonWeylFamily c f)) =
      (complexify f).eval
        (z (some ()) * (1 - (c : ℂ) * z none)) := by
  rw [BorceaBranden.signedWeylSymbol]
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_rename,
    Function.comp_apply, MvPolynomial.eval_C, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, poissonWeylFamily, eval_polynomialToMv,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (c : ℂ) ^ j * z (some ()) ^ j *
      (hasseDeriv j (complexify f)).eval (z (some ())) *
        (-1) ^ j * z none ^ j) (f.natDegree + 1)]
  have hdegree : (complexify f).natDegree = f.natDegree := by
    unfold complexify
    exact Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective f
  simpa only [hdegree] using
    sum_hasseDeriv_scale (complexify f) (c : ℂ) (z (some ())) (z none)

private theorem signedWeylSymbol_poissonWeylFamily_stable
    {c : ℝ} {f : ℝ[X]} (hf : IsAdmissible c f) :
    MvUpperHalfPlaneStable
      (BorceaBranden.signedWeylSymbol f.natDegree
        (poissonWeylFamily c f)) := by
  intro z hz
  rw [eval_signedWeylSymbol_poissonWeylFamily]
  let w : Fin 2 → ℂ := ![z (some ()), z none]
  have hw : ∀ i, 0 < (w i).im := by
    intro i
    fin_cases i
    · exact hz (some ())
    · exact hz none
  have hstable := hf.poissonSignedSymbol_stable w hw
  rw [eval_poissonSignedSymbol] at hstable
  exact hstable

private theorem finiteOrderWeylOperator_poissonWeylFamily
    (c : ℝ) (f g : ℝ[X]) :
    BorceaBranden.finiteOrderWeylOperator () f.natDegree
        (poissonWeylFamily c f) (polynomialToMv (complexify g)) =
      polynomialToMv (complexify (starC c f g)) := by
  rw [BorceaBranden.finiteOrderWeylOperator]
  change (∑ j : Fin (f.natDegree + 1),
      poissonWeylFamily c f j *
        iteratedPDerivAt () (j : ℕ) (polynomialToMv (complexify g))) = _
  simp only [poissonWeylFamily, iteratedPDerivAt_polynomialToMv]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    polynomialToMv
        (C ((c : ℂ) ^ j) * X ^ j * hasseDeriv j (complexify f)) *
      polynomialToMv ((derivative^[j]) (complexify g)))
      (f.natDegree + 1)]
  rw [starC]
  rw [complexify_finset_sum]
  rw [polynomialToMv_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [C_pow_mul_hasseDeriv_eq, ← polynomialToMv_mul]
  congr 1
  rw [← complexify_iterate_derivative]
  exact (Polynomial.map_mul Complex.ofRealHom).symm

/-- An admissible fixed left factor sends every nonzero split polynomial to
a split polynomial or zero under the Poisson product. -/
theorem IsAdmissible.preservesRealRootedOrZero {c : ℝ} {f : ℝ[X]}
    (hf : IsAdmissible c f) :
    PreservesRealRootedOrZero (starCLinearMap c f) := by
  intro g hg
  have hgStable : MvUpperHalfPlaneStable
      (polynomialToMv (complexify g)) := by
    intro z hz
    rw [eval_polynomialToMv]
    exact Polynomial.Splits.isUpperHalfPlaneStable_complexify hg.2 hg.1
      (z ()) (hz ())
  have hout := BorceaBranden.finiteOrderWeylOperator_preserves_stability
    () f.natDegree (poissonWeylFamily c f)
    (signedWeylSymbol_poissonWeylFamily_stable hf) hgStable
  rw [finiteOrderWeylOperator_poissonWeylFamily] at hout
  rcases hout with hzero | hstable
  · left
    rw [starCLinearMap_apply]
    have hcomplex : complexify (starC c f g) = 0 := by
      apply polynomialToMv_injective
      rw [hzero]
      simp [polynomialToMv]
    exact (Polynomial.map_eq_zero_iff Complex.ofReal_injective).mp hcomplex
  · right
    rw [starCLinearMap_apply]
    apply IsUpperHalfPlaneStable.splits_complexify
    intro z hz
    have heval := hstable (fun _ : Unit => z) (fun _ => hz)
    simpa only [eval_polynomialToMv] using heval

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
