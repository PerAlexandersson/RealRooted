import RealRooted.CombinatorialExamples.MultisetEulerianNarayana.GammaOperator
import RealRooted.OperatorInterlacingUpgrade.ImplicitRoot

/-!
# Monotonicity of the zeros of the gamma operator

Zhang--Zhao (arXiv:2610.00966), Proposition 3.4.  Let `p = ∏ (X - r_j)` have simple negative
roots, let `a > 0` and `d ∈ {2n, 2n + 1}` for `n = deg p`.  Every root `ρ` of
`Φ_{d,a} p = p + (z(1 - 4z) p' + 2dz p) / a` is simple (`simpleNegRooted_gammaOperator`) and
moves along a differentiable branch in each parameter:

* `exists_hasDerivAt_gammaOperator_input_shift`: the branch has strictly positive derivative
  when one input root `r_i` is moved to the right;
* `exists_hasDerivAt_gammaOperator_parameter_shift`: the branch has strictly negative derivative
  when `a` increases.

The sign comes from the strict interlacing of `p` with the numerator `Φ_{d,a} p` supplied by
`strictInterl_gammaOperatorNumerator`: `p(ρ) (Φ p)'(ρ) > 0` at every root `ρ` of `Φ p`.
Both signs are derived from it: for the input roots through the deletion identity
`T((X - r_i) q) = (X - r_i) T q + z(1 - 4z) q`, and for `a` directly.
-/

open Polynomial
open scoped ContDiff
open scoped Topology

noncomputable section

namespace RealRooted
namespace MultisetEulerianNarayana

/-- The linear numerator operator underlying `gammaOperatorNumerator`. -/
def gammaOperatorNumeratorLinear (d : ℕ) (a : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  LinearMap.mulLeft ℝ (C a) +
    (LinearMap.mulLeft ℝ (X * (1 - C 4 * X))).comp Polynomial.derivative +
      LinearMap.mulLeft ℝ (C (2 * (d : ℝ)) * X)

/-- Applying the linear numerator operator agrees with the polynomial definition. -/
theorem gammaOperatorNumeratorLinear_apply (d : ℕ) (a : ℝ) (f : ℝ[X]) :
    gammaOperatorNumeratorLinear d a f = gammaOperatorNumerator d a f := by
  simp only [gammaOperatorNumeratorLinear, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply]
  rfl

/-- Raising `a` adds a multiple of the input to the numerator. -/
theorem gammaOperatorNumerator_add_left (d : ℕ) (a s : ℝ) (f : ℝ[X]) :
    gammaOperatorNumerator d (a + s) f = gammaOperatorNumerator d a f + C s * f := by
  simp only [gammaOperatorNumerator, C_add]
  ring

/-- Deletion identity: the numerator of a product with a linear factor. -/
theorem gammaOperatorNumerator_X_sub_C_mul (d : ℕ) (a c : ℝ) (q : ℝ[X]) :
    gammaOperatorNumerator d a ((X - C c) * q) =
      (X - C c) * gammaOperatorNumerator d a q + X * (1 - C 4 * X) * q := by
  simp only [gammaOperatorNumerator, derivative_mul, derivative_sub, derivative_X,
    derivative_C, sub_zero, one_mul]
  ring

private theorem finRootPolynomial_eq_prod {n : ℕ} (r : Fin n → ℝ) :
    finRootPolynomial r = ∏ j : Fin n, (X - C (r j)) := by
  simp [finRootPolynomial, rootPolynomial, List.prod_ofFn]

private theorem isRoot_finRootPolynomial {n : ℕ} (r : Fin n → ℝ) (i : Fin n) :
    (finRootPolynomial r).IsRoot (r i) := by
  rw [IsRoot.def, finRootPolynomial_eq_prod, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- A finite vector of distinct negative numbers gives a `SimpleNegRooted` root polynomial. -/
theorem simpleNegRooted_finRootPolynomial {n : ℕ} {r : Fin n → ℝ} (hneg : ∀ j, r j < 0)
    (hinj : Function.Injective r) : SimpleNegRooted (finRootPolynomial r) n := by
  have hmonic := rootPolynomial_monic ((Finset.univ : Finset (Fin n)).val.map r)
  refine ⟨by simp [finRootPolynomial], ?_, ?_, ?_, rootPolynomial_splits _, ?_⟩
  · unfold HasPosLeadingCoeff
    rw [finRootPolynomial, hmonic.leadingCoeff]
    exact one_pos
  · rw [finRootPolynomial_eq_prod]
    exact hasNonnegCoeffs_finsetProd Finset.univ (fun j => X - C (r j))
      (fun j _ => hasNonnegCoeffs_X_sub_C (hneg j).le)
  · rw [coeff_zero_eq_eval_zero, finRootPolynomial_eq_prod, eval_prod]
    exact Finset.prod_pos fun j _ => by simpa using hneg j
  · intro ρ hρ
    rw [← count_roots, finRootPolynomial, roots_rootPolynomial]
    apply Multiset.count_eq_one_of_mem (Multiset.Nodup.map hinj Finset.univ.nodup)
    rw [← roots_rootPolynomial ((Finset.univ : Finset (Fin n)).val.map r)]
    exact (mem_roots hmonic.ne_zero).mpr hρ

private theorem gammaOperatorNumerator_simpleNegRooted {d q : ℕ} {a : ℝ} {f : ℝ[X]}
    (ha : 0 < a) (h : SimpleNegRooted (gammaOperator d a f) q) :
    SimpleNegRooted (gammaOperatorNumerator d a f) q := by
  have hmul := h.C_mul ha
  have he : C a * gammaOperator d a f = gammaOperatorNumerator d a f := by
    rw [gammaOperator, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha.ne', C_1, one_mul]
  rwa [he] at hmul

/-- At a root `ρ` of the gamma numerator of a `SimpleNegRooted` input `f`, the root is negative
and simple, and `f(ρ) T f'(ρ) > 0` (strict interlacing of `f` with `T f`). -/
theorem gammaOperatorNumerator_root_data {d m : ℕ} {a : ℝ} {f : ℝ[X]} (hmpos : m ≠ 0)
    (ha : 0 < a) (hf : SimpleNegRooted f m) (hd : d = 2 * m ∨ d = 2 * m + 1) {ρ : ℝ}
    (hρ : (gammaOperatorNumerator d a f).IsRoot ρ) :
    ρ < 0 ∧ (gammaOperatorNumerator d a f).derivative.eval ρ ≠ 0 ∧
      0 < f.eval ρ * (gammaOperatorNumerator d a f).derivative.eval ρ := by
  obtain ⟨q, hq, hΦ⟩ : ∃ q, (q = m ∨ q = m + 1) ∧
      SimpleNegRooted (gammaOperator d a f) q := by
    rcases simpleNegRooted_gammaOperator_of_pos_natDegree hmpos ha hf hd with
      ⟨_, h⟩ | ⟨_, h⟩
    · exact ⟨m, Or.inl rfl, h⟩
    · exact ⟨m + 1, Or.inr rfl, h⟩
  have hG := gammaOperatorNumerator_simpleNegRooted ha hΦ
  obtain ⟨hint, hno, -⟩ := strictInterl_gammaOperatorNumerator hf.natDegree_eq hmpos hf
    hG.nonneg hG.coeff_zero_pos (by rw [hG.natDegree_eq]; exact hq)
  have hder := hG.simple.eval_derivative_ne_zero hρ
  have hnn := hint.eval_mul_eval_derivative_nonneg hf.pos hG.pos hρ
  have hf0 : f.eval ρ ≠ 0 := fun h => hno ρ (IsRoot.def.mpr h) hρ
  exact ⟨hG.isRoot_neg hρ, hder, lt_of_le_of_ne hnn (Ne.symm (mul_ne_zero hf0 hder))⟩

/-- The quotient driving the input-root derivative is strictly positive at a root of the
numerator. -/
private theorem gammaOperatorNumerator_input_quotient_pos {n d : ℕ} {a : ℝ} {r : Fin n → ℝ}
    (ha : 0 < a) (hr : ∀ j, r j < 0) (hinj : Function.Injective r)
    (hd : d = 2 * n ∨ d = 2 * n + 1) (i : Fin n) {ρ : ℝ}
    (hρ : (gammaOperatorNumerator d a (finRootPolynomial r)).IsRoot ρ) :
    0 < (gammaOperatorNumerator d a (finRootPolynomial r / (X - C (r i)))).eval ρ /
      (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ := by
  have hp := simpleNegRooted_finRootPolynomial hr hinj
  obtain ⟨hρneg, hder, hpos⟩ := gammaOperatorNumerator_root_data (Fin.pos i).ne' ha hp hd hρ
  set q : ℝ[X] := finRootPolynomial r / (X - C (r i)) with hqdef
  have hfactor : (X - C (r i)) * q = finRootPolynomial r :=
    IsRoot.mul_div_eq (isRoot_finRootPolynomial r i)
  have hpeval : (finRootPolynomial r).eval ρ = (ρ - r i) * q.eval ρ := by
    rw [← hfactor]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
  have hne : ρ - r i ≠ 0 := by
    intro h0
    rw [hpeval, h0, zero_mul, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hrel := gammaOperatorNumerator_X_sub_C_mul d a (r i) q
  rw [hfactor] at hrel
  have hzero : (ρ - r i) * (gammaOperatorNumerator d a q).eval ρ +
      ρ * (1 - 4 * ρ) * q.eval ρ = 0 := by
    have h0 := congrArg (Polynomial.eval ρ) hrel
    rw [hρ.eq_zero] at h0
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one] at h0
    linarith
  have hkey : (ρ - r i) ^ 2 * ((gammaOperatorNumerator d a q).eval ρ *
      (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ) =
      (-(ρ * (1 - 4 * ρ))) * ((finRootPolynomial r).eval ρ *
        (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ) := by
    rw [hpeval]
    linear_combination (ρ - r i) *
      (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ * hzero
  have hfac : 0 < -(ρ * (1 - 4 * ρ)) := by nlinarith
  have hprod : 0 < (ρ - r i) ^ 2 * ((gammaOperatorNumerator d a q).eval ρ *
      (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ) := by
    rw [hkey]
    exact mul_pos hfac hpos
  have hprod' := (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hne)).mp hprod
  have hsq := mul_self_pos.mpr hder
  have hdiv := div_pos hprod' hsq
  rwa [mul_div_mul_right _ _ hder] at hdiv

private theorem eval_gammaOperator_div_derivative {d : ℕ} {a : ℝ} (ha : 0 < a) (f g : ℝ[X])
    (ρ : ℝ) :
    (gammaOperator d a f).eval ρ / (gammaOperator d a g).derivative.eval ρ =
      (gammaOperatorNumerator d a f).eval ρ /
        (gammaOperatorNumerator d a g).derivative.eval ρ := by
  simp only [gammaOperator, eval_mul, eval_C, derivative_C_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero ha.ne')

private theorem isRoot_gammaOperator_iff {d : ℕ} {a : ℝ} (ha : 0 < a) (f : ℝ[X]) (ρ : ℝ) :
    (gammaOperator d a f).IsRoot ρ ↔ (gammaOperatorNumerator d a f).IsRoot ρ := by
  simp only [gammaOperator, IsRoot.def, eval_mul, eval_C, mul_eq_zero, inv_eq_zero, ha.ne',
    false_or]

/-- **Zhang--Zhao, Proposition 3.4 (input roots).**  Let `p = ∏ (X - r_j)` have distinct negative
roots, `a > 0`, and `d = 2n` or `d = 2n + 1` with `n = deg p`.  At a root `ρ` of `Φ_{d,a} p`
(automatically simple), moving the input root `r_i` to `r_i + s` moves `ρ` along a differentiable
branch `ρ(s)` whose derivative at `0` is the displayed quotient, which is strictly positive. -/
theorem exists_hasDerivAt_gammaOperator_input_shift
    {n d : ℕ} {a : ℝ} {r : Fin n → ℝ} (ha : 0 < a) (hr : ∀ j, r j < 0)
    (hinj : Function.Injective r) (hd : d = 2 * n ∨ d = 2 * n + 1) (i : Fin n) {ρ : ℝ}
    (hρ : (gammaOperator d a (finRootPolynomial r)).IsRoot ρ) :
    ∃ branch : ℝ → ℝ,
      HasDerivAt branch
        ((gammaOperator d a (finRootPolynomial r / (X - C (r i)))).eval ρ /
          (gammaOperator d a (finRootPolynomial r)).derivative.eval ρ) 0 ∧
      0 < (gammaOperator d a (finRootPolynomial r / (X - C (r i)))).eval ρ /
          (gammaOperator d a (finRootPolynomial r)).derivative.eval ρ ∧
      branch 0 = ρ ∧
      ∀ᶠ s in 𝓝 0,
        (gammaOperator d a (finRootPolynomial (Function.update r i (r i + s)))).IsRoot
          (branch s) := by
  have hp := simpleNegRooted_finRootPolynomial hr hinj
  have hρ' := (isRoot_gammaOperator_iff ha _ ρ).mp hρ
  obtain ⟨-, hder, -⟩ := gammaOperatorNumerator_root_data (Fin.pos i).ne' ha hp hd hρ'
  have hquot := gammaOperatorNumerator_input_quotient_pos ha hr hinj hd i hρ'
  have hρlin : (gammaOperatorNumeratorLinear d a (finRootPolynomial r)).IsRoot ρ := by
    rwa [gammaOperatorNumeratorLinear_apply]
  have hderlin :
      (gammaOperatorNumeratorLinear d a (finRootPolynomial r)).derivative.eval ρ ≠ 0 := by
    rwa [gammaOperatorNumeratorLinear_apply]
  obtain ⟨branch, hbranch, hbase, hroots⟩ :=
    exists_hasDerivAt_finRootPolynomial_shift (i := i) hρlin hderlin
  simp only [gammaOperatorNumeratorLinear_apply] at hbranch hroots
  rw [← eval_gammaOperator_div_derivative ha] at hbranch hquot
  refine ⟨branch, hbranch, hquot, hbase, ?_⟩
  filter_upwards [hroots] with s hs
  exact (isRoot_gammaOperator_iff ha _ _).mpr hs

/-- One-variable implicit root of `P + s Q` at a simple root of `P`. -/
private theorem exists_hasDerivAt_isRoot_add_C_mul {P Q : ℝ[X]} {ρ : ℝ}
    (hroot : P.IsRoot ρ) (hregular : P.derivative.eval ρ ≠ 0) :
    ∃ branch : ℝ → ℝ,
      HasDerivAt branch (-Q.eval ρ / P.derivative.eval ρ) 0 ∧ branch 0 = ρ ∧
        ∀ᶠ s in 𝓝 0, (P + C s * Q).IsRoot (branch s) := by
  let F : ℝ × ℝ → ℝ := fun z => P.eval z.2 + z.1 * Q.eval z.2
  have hglobal : ContDiff ℝ ∞ F := by
    dsimp [F]
    exact (((Polynomial.contDiff_aeval P ∞).comp contDiff_snd).add
      (contDiff_fst.mul ((Polynomial.contDiff_aeval Q ∞).comp contDiff_snd)))
  have hcont : ContDiffAt ℝ ∞ F (0, ρ) := hglobal.contDiffAt
  let A : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (0, ρ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  let B : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (0, ρ) ∘L ContinuousLinearMap.inl ℝ ℝ ℝ
  have hfull : HasFDerivAt F (fderiv ℝ F (0, ρ)) (0, ρ) :=
    (hcont.differentiableAt (by simp)).hasFDerivAt
  have hA : A = ContinuousLinearMap.toSpanSingleton ℝ (P.derivative.eval ρ) := by
    apply HasFDerivAt.unique
    · exact hfull.comp ρ (hasFDerivAt_prodMk_right 0 ρ)
    · convert P.hasFDerivAt ρ using 1
      · funext x
        simp [F]
      · apply ContinuousLinearMap.ext
        intro x
        simp
  have hparam : HasDerivAt (fun s => F (s, ρ)) (Q.eval ρ) 0 := by
    convert ((hasDerivAt_const 0 (P.eval ρ)).add
      ((hasDerivAt_id 0).mul_const (Q.eval ρ))) using 1
    · funext s
      simp [F]
    · simp
  have hB : B = ContinuousLinearMap.toSpanSingleton ℝ (Q.eval ρ) := by
    apply HasFDerivAt.unique
    · exact hfull.comp 0 (hasFDerivAt_prodMk_left 0 ρ)
    · exact hparam.hasFDerivAt
  have hAinv : A.IsInvertible := by
    rw [hA]
    exact ContinuousLinearMap.isInvertible_toSpanSingleton hregular
  let branch : ℝ → ℝ := hcont.implicitFunction (by simp) hAinv
  have hbase : branch 0 = ρ :=
    hcont.implicitFunction_apply_self (by simp) hAinv
  have hFzero : F (0, ρ) = 0 := by
    simpa only [F, zero_mul, add_zero, IsRoot.def] using hroot
  have hbranch : ∀ᶠ s in 𝓝 0, F (s, branch s) = 0 := by
    have heq := hcont.eventually_apply_implicitFunction (by simp) hAinv
    filter_upwards [heq] with s hs
    exact hs.trans hFzero
  have hstrict := hcont.hasStrictFDerivAt_implicitFunction (by simp) hAinv
  have hbranchDeriv : HasDerivAt branch ((-(A.inverse ∘L B)) 1) 0 := by
    simpa only [branch, A, B] using hstrict.hasFDerivAt.hasDerivAt
  have hquotient : (-(A.inverse ∘L B)) 1 = -Q.eval ρ / P.derivative.eval ρ := by
    rw [neg_apply, ContinuousLinearMap.comp_apply, hB,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, hA]
    rw [ContinuousLinearMap.inverse_toSpanSingleton_apply hregular]
    ring
  refine ⟨branch, ?_, hbase, ?_⟩
  · simpa only [hquotient] using hbranchDeriv
  · filter_upwards [hbranch] with s hs
    simpa only [F, IsRoot.def, eval_add, eval_mul, eval_C] using hs

/-- **Zhang--Zhao, Proposition 3.4 (parameter).**  Let `p = ∏ (X - r_j)` have distinct negative
roots (`n ≠ 0`), `a > 0`, and `d = 2n` or `d = 2n + 1` with `n = deg p`.  At a root `ρ` of
`Φ_{d,a} p`, the root moves along a differentiable branch `ρ(s)` of `Φ_{d,a+s} p` whose
derivative at `0` is strictly negative (the displayed quotient is `-p(ρ) / T p'(ρ)` for the
numerator `T p = a Φ_{d,a} p`). -/
theorem exists_hasDerivAt_gammaOperator_parameter_shift
    {n d : ℕ} {a : ℝ} {r : Fin n → ℝ} (hn : n ≠ 0) (ha : 0 < a) (hr : ∀ j, r j < 0)
    (hinj : Function.Injective r) (hd : d = 2 * n ∨ d = 2 * n + 1) {ρ : ℝ}
    (hρ : (gammaOperator d a (finRootPolynomial r)).IsRoot ρ) :
    ∃ branch : ℝ → ℝ,
      HasDerivAt branch
        (-(finRootPolynomial r).eval ρ /
          (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ) 0 ∧
      -(finRootPolynomial r).eval ρ /
          (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ < 0 ∧
      branch 0 = ρ ∧
      ∀ᶠ s in 𝓝 0, (gammaOperator d (a + s) (finRootPolynomial r)).IsRoot (branch s) := by
  have hp := simpleNegRooted_finRootPolynomial hr hinj
  have hρ' := (isRoot_gammaOperator_iff ha _ ρ).mp hρ
  obtain ⟨-, hder, hpos⟩ := gammaOperatorNumerator_root_data hn ha hp hd hρ'
  obtain ⟨branch, hbranch, hbase, hroots⟩ := exists_hasDerivAt_isRoot_add_C_mul
    (Q := finRootPolynomial r) hρ' hder
  have hneg : -(finRootPolynomial r).eval ρ /
      (gammaOperatorNumerator d a (finRootPolynomial r)).derivative.eval ρ < 0 := by
    have hdiv := div_pos hpos (mul_self_pos.mpr hder)
    rw [mul_div_mul_right _ _ hder] at hdiv
    rw [neg_div, neg_lt_zero]
    exact hdiv
  refine ⟨branch, hbranch, hneg, hbase, ?_⟩
  filter_upwards [hroots] with s hs
  rw [gammaOperator, IsRoot.def, eval_mul, gammaOperatorNumerator_add_left]
  rw [IsRoot.def] at hs
  rw [hs, mul_zero]

end MultisetEulerianNarayana
end RealRooted
