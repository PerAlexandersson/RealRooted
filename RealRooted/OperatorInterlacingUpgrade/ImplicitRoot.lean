import RealRooted.CriticalValueContinuation
import RealRooted.OperatorInterlacingUpgrade.RootOrder
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Implicit root motion under a linear operator

Let `T` be a linear operator, `p_r = ∏ j, (X - r_j)` and `ρ` a simple root of `T p_r`.  Moving
the input root `r_i` to `r_i + s` moves `ρ` along a differentiable branch `ρ(s)` with
`ρ'(0) = T(p_r / (X - r_i))(ρ) / (T p_r)'(ρ)`
(`exists_hasDerivAt_finRootPolynomial_shift`, by the one-variable implicit function theorem).
For a monomial-chain operator and nonpositive input roots the derivative is nonnegative
(`finRootPolynomial_shift_deriv_nonneg_of_monomialChain`): `T(p_r / (X - r_i))` interlaces
`T p_r`, so output roots move right when an input root moves right.
-/

open Polynomial
open scoped BigOperators
open scoped ContDiff
open scoped Topology

noncomputable section

namespace RealRooted

/-- The repository root polynomial attached to a finite root vector. -/
abbrev finRootPolynomial {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  rootPolynomial ((Finset.univ : Finset (Fin n)).val.map r)

/-- The finite-vector notation is definitionally the repository multiset notation. -/
theorem finRootPolynomial_eq_rootPolynomial {n : ℕ} (r : Fin n → ℝ) :
    finRootPolynomial r = rootPolynomial ((Finset.univ : Finset (Fin n)).val.map r) := rfl

private theorem finRootPolynomial_eq_finset_prod {n : ℕ} (r : Fin n → ℝ) :
    finRootPolynomial r = ∏ j : Fin n, (X - C (r j)) := by
  simp [finRootPolynomial, rootPolynomial, List.prod_ofFn]

/-- Shifting one root gives the exact affine polynomial family used below. -/
theorem finRootPolynomial_shift_eq_sub_mul_div
    {n : ℕ} (r : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    finRootPolynomial (Function.update r i (r i + s)) =
      finRootPolynomial r - C s * (finRootPolynomial r / (X - C (r i))) := by
  let q : ℝ[X] := finRootPolynomial r / (X - C (r i))
  have hroot : (finRootPolynomial r).IsRoot (r i) := by
    rw [Polynomial.IsRoot.def, finRootPolynomial_eq_finset_prod, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hfactor : (X - C (r i)) * q = finRootPolynomial r := by
    exact IsRoot.mul_div_eq hroot
  have hprod : (X - C (r i)) *
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (r j)) =
      finRootPolynomial r := by
    rw [finRootPolynomial_eq_finset_prod]
    exact
      (Finset.mul_prod_erase Finset.univ (fun j => X - C (r j)) (Finset.mem_univ i))
  have hq : q = ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (r j)) := by
    apply mul_left_cancel₀ (X_sub_C_ne_zero (r i))
    rw [hfactor, hprod]
  have hrest :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        (X - C ((Function.update r i (r i + s)) j))) =
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (r j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update, Finset.ne_of_mem_erase hj]
  rw [finRootPolynomial_eq_finset_prod]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun j => X - C ((Function.update r i (r i + s)) j)) (Finset.mem_univ i)]
  rw [Function.update_self, hrest, ← hq]
  rw [map_add]
  change _ = finRootPolynomial r - C s * q
  rw [← hfactor]
  ring

private theorem finRootPolynomial_div_factor_eq_delete
    {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    finRootPolynomial r / (X - C (r i)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (r j)) := by
  have hroot : (finRootPolynomial r).IsRoot (r i) := by
    rw [Polynomial.IsRoot.def, finRootPolynomial_eq_finset_prod, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hfactor : (X - C (r i)) *
      (finRootPolynomial r / (X - C (r i))) = finRootPolynomial r :=
    IsRoot.mul_div_eq hroot
  have hprod : (X - C (r i)) *
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (X - C (r j)) =
      finRootPolynomial r := by
    rw [finRootPolynomial_eq_finset_prod]
    exact
      (Finset.mul_prod_erase Finset.univ (fun j => X - C (r j)) (Finset.mem_univ i))
  apply mul_left_cancel₀ (X_sub_C_ne_zero (r i))
  rw [hfactor, hprod]

private theorem hasNonnegCoeffs_finRootPolynomial_of_nonpos
    {n : ℕ} {r : Fin n → ℝ} (hr : ∀ j, r j ≤ 0) :
    HasNonnegCoeffs (finRootPolynomial r) := by
  rw [finRootPolynomial_eq_finset_prod]
  exact hasNonnegCoeffs_finsetProd Finset.univ (fun j => X - C (r j))
    (fun j _ => hasNonnegCoeffs_X_sub_C (hr j))

private theorem hasNonnegCoeffs_finRootPolynomial_div_factor_of_nonpos
    {n : ℕ} {r : Fin n → ℝ} (i : Fin n) (hr : ∀ j, r j ≤ 0) :
    HasNonnegCoeffs (finRootPolynomial r / (X - C (r i))) := by
  rw [finRootPolynomial_div_factor_eq_delete]
  exact hasNonnegCoeffs_finsetProd _ (fun j => X - C (r j))
    (fun j _ => hasNonnegCoeffs_X_sub_C (hr j))

private theorem strictInterl_finRootPolynomial_div_factor
    {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    StrictInterl (finRootPolynomial r / (X - C (r i))) (finRootPolynomial r) := by
  have hpne : finRootPolynomial r ≠ 0 :=
    (rootPolynomial_monic ((Finset.univ : Finset (Fin n)).val.map r)).ne_zero
  have hpsplits : (finRootPolynomial r).Splits := by
    exact rootPolynomial_splits ((Finset.univ : Finset (Fin n)).val.map r)
  have hroot : (finRootPolynomial r).IsRoot (r i) := by
    rw [Polynomial.IsRoot.def, finRootPolynomial_eq_finset_prod, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hfactor : (X - C (r i)) *
      (finRootPolynomial r / (X - C (r i))) = finRootPolynomial r :=
    IsRoot.mul_div_eq hroot
  have hqne : finRootPolynomial r / (X - C (r i)) ≠ 0 := by
    intro hq
    apply hpne
    rw [← hfactor, hq, mul_zero]
  have hqdvd : finRootPolynomial r / (X - C (r i)) ∣ finRootPolynomial r := by
    refine ⟨X - C (r i), ?_⟩
    rw [mul_comm, hfactor]
  have hqrr := isRealRooted_of_dvd hpne hpsplits hqne hqdvd
  have hstrict := strictInterl_self_X_sub_C_mul hqrr.1 hqrr.2 (r i)
  rw [hfactor] at hstrict
  exact hstrict

/- The local branch theorem below is the one-dimensional implicit-function
calculation.  The quotient is positive in the usual monomial-chain situation;
the sign statement is kept separate because it needs the interlacing API. -/

/--
A simple output root has a differentiable branch under one input-root move.
The shifted input polynomial has derivative `-p/(X-C (r i))`; the two minus
signs in the implicit equation therefore give the displayed positive quotient.
-/
theorem exists_hasDerivAt_finRootPolynomial_shift
    {n : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {r : Fin n → ℝ} {i : Fin n} {ρ : ℝ}
    (hroot : (T (finRootPolynomial r)).IsRoot ρ)
    (hregular : (T (finRootPolynomial r)).derivative.eval ρ ≠ 0) :
    ∃ branch : ℝ → ℝ,
      HasDerivAt branch
        ((T (finRootPolynomial r / (X - C (r i)))).eval ρ /
          (T (finRootPolynomial r)).derivative.eval ρ) 0 ∧
        branch 0 = ρ ∧
          ∀ᶠ s in 𝓝 0,
            (T (finRootPolynomial (Function.update r i (r i + s)))).IsRoot (branch s) := by
  let p : ℝ[X] := finRootPolynomial r
  let q : ℝ[X] := p / (X - C (r i))
  let F : ℝ × ℝ → ℝ := fun z =>
    (T p).eval z.2 - z.1 * (T q).eval z.2
  have hglobal : ContDiff ℝ ∞ F := by
    dsimp [F]
    exact (((Polynomial.contDiff_aeval (T p) ∞).comp contDiff_snd).sub
      (contDiff_fst.mul ((Polynomial.contDiff_aeval (T q) ∞).comp contDiff_snd)))
  have hcont : ContDiffAt ℝ ∞ F (0, ρ) := hglobal.contDiffAt
  let A : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (0, ρ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  let B : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (0, ρ) ∘L ContinuousLinearMap.inl ℝ ℝ ℝ
  have hfull : HasFDerivAt F (fderiv ℝ F (0, ρ)) (0, ρ) :=
    (hcont.differentiableAt (by simp)).hasFDerivAt
  have hA : A = ContinuousLinearMap.toSpanSingleton ℝ
      ((T p).derivative.eval ρ) := by
    apply HasFDerivAt.unique
    · exact hfull.comp ρ (hasFDerivAt_prodMk_right 0 ρ)
    · convert (T p).hasFDerivAt ρ using 1
      · funext x
        simp [F]
      · apply ContinuousLinearMap.ext
        intro x
        simp
  have hparam : HasDerivAt (fun s => F (s, ρ)) (-(T q).eval ρ) 0 := by
    convert ((hasDerivAt_const 0 ((T p).eval ρ)).sub
      ((hasDerivAt_id 0).const_mul ((T q).eval ρ))) using 1
    · funext s
      dsimp [F]
      ring
    · ring
  have hB : B = ContinuousLinearMap.toSpanSingleton ℝ (-(T q).eval ρ) := by
    apply HasFDerivAt.unique
    · exact hfull.comp 0 (hasFDerivAt_prodMk_left 0 ρ)
    · exact hparam.hasFDerivAt
  have hregular' : (T p).derivative.eval ρ ≠ 0 := by
    simpa only [p] using hregular
  have hAinv : A.IsInvertible := by
    rw [hA]
    exact ContinuousLinearMap.isInvertible_toSpanSingleton hregular'
  let branch : ℝ → ℝ := hcont.implicitFunction (by simp) hAinv
  have hbase : branch 0 = ρ :=
    hcont.implicitFunction_apply_self (by simp) hAinv
  have hFzero : F (0, ρ) = 0 := by
    simpa only [F, zero_mul, sub_zero, p, Polynomial.IsRoot.def] using hroot
  have hbranch : ∀ᶠ s in 𝓝 0, F (s, branch s) = 0 := by
    have heq := hcont.eventually_apply_implicitFunction (by simp) hAinv
    filter_upwards [heq] with s hs
    exact hs.trans hFzero
  have hrootEvent : ∀ᶠ s in 𝓝 0,
      (T (finRootPolynomial (Function.update r i (r i + s)))).IsRoot (branch s) := by
    have hpoly : ∀ s : ℝ,
        finRootPolynomial (Function.update r i (r i + s)) = p - s • q := by
      intro s
      simpa only [p, q, smul_eq_C_mul] using
        finRootPolynomial_shift_eq_sub_mul_div r i s
    filter_upwards [hbranch] with s hs
    rw [Polynomial.IsRoot.def, hpoly, map_sub, map_smul, eval_sub, eval_smul]
    simpa only [F, smul_eq_mul] using hs
  have hstrict := hcont.hasStrictFDerivAt_implicitFunction (by simp) hAinv
  have hbranchDeriv : HasDerivAt branch ((-(A.inverse ∘L B)) 1) 0 := by
    simpa only [branch, A, B] using hstrict.hasFDerivAt.hasDerivAt
  have hquotient : (-(A.inverse ∘L B)) 1 =
      (T q).eval ρ / (T p).derivative.eval ρ := by
    rw [neg_apply, ContinuousLinearMap.comp_apply, hB,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, hA]
    rw [ContinuousLinearMap.inverse_toSpanSingleton_apply hregular']
    ring
  refine ⟨branch, ?_, hbase, hrootEvent⟩
  simpa only [hquotient, p, q] using hbranchDeriv

/--
For a monomial-chain operator, the existing oriented-interlacing theorem
supplies `hinter` below.  If the input roots are nonpositive, both input
polynomials have nonnegative coefficients automatically, so the output
nonnegativity assumptions needed by the sign lemma are also automatic.
-/
theorem finRootPolynomial_shift_deriv_nonneg_of_strictInterl
    {n : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {r : Fin n → ℝ} {i : Fin n} {ρ : ℝ}
    (hr : ∀ j, r j ≤ 0)
    (hinter : StrictInterl
      (T (finRootPolynomial r / (X - C (r i)))) (T (finRootPolynomial r)))
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hroot : (T (finRootPolynomial r)).IsRoot ρ)
    (hregular : (T (finRootPolynomial r)).derivative.eval ρ ≠ 0) :
    0 ≤ (T (finRootPolynomial r / (X - C (r i)))).eval ρ /
      (T (finRootPolynomial r)).derivative.eval ρ := by
  have hpnn : HasNonnegCoeffs (finRootPolynomial r) :=
    hasNonnegCoeffs_finRootPolynomial_of_nonpos hr
  have hqnn : HasNonnegCoeffs (finRootPolynomial r / (X - C (r i))) :=
    hasNonnegCoeffs_finRootPolynomial_div_factor_of_nonpos i hr
  have hprod := hinter.eval_mul_eval_derivative_nonneg
    ((hTnn hqnn).pos_leadingCoeff hinter.1.1)
    ((hTnn hpnn).pos_leadingCoeff hinter.2.1.1) hroot
  rcases lt_or_gt_of_ne hregular with hder_neg | hder_pos
  · exact div_nonneg_of_nonpos (by nlinarith) hder_neg.le
  · exact div_nonneg (by nlinarith) hder_pos.le

/-- The derivative is nonnegative under the monomial-chain hypotheses. -/
theorem finRootPolynomial_shift_deriv_nonneg_of_monomialChain
    {n D : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {r : Fin n → ℝ} {i : Fin n} {ρ : ℝ}
    (hr : ∀ j, r j ≤ 0)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1))))
    (hD : n ≤ D)
    (hroot : (T (finRootPolynomial r)).IsRoot ρ)
    (hregular : (T (finRootPolynomial r)).derivative.eval ρ ≠ 0) :
    0 ≤ (T (finRootPolynomial r / (X - C (r i)))).eval ρ /
      (T (finRootPolynomial r)).derivative.eval ρ := by
  have hpnn : HasNonnegCoeffs (finRootPolynomial r) :=
    hasNonnegCoeffs_finRootPolynomial_of_nonpos hr
  have hqnn : HasNonnegCoeffs (finRootPolynomial r / (X - C (r i))) :=
    hasNonnegCoeffs_finRootPolynomial_div_factor_of_nonpos i hr
  have hinter := strictInterl_finRootPolynomial_div_factor r i
  have hdegree : (finRootPolynomial r).natDegree ≤ D := by
    rw [finRootPolynomial, natDegree_rootPolynomial, Multiset.card_map]
    simpa using hD
  have hmap := strictInterl_map_of_monomialChain hinter hqnn hpnn hdegree hTnn hTrr hmono
  exact finRootPolynomial_shift_deriv_nonneg_of_strictInterl hr hmap hTnn hroot hregular

end RealRooted
