import RealRooted.Gurvits.Univariate
import RealRooted.Gurvits.Capacity
import RealRooted.MultivariateStability.Specialization
import RealRooted.MultivariateStability.LinearForm
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.Derivative
import RealRooted.HermiteBiehler.Basic

/-!
# Gurvits' capacity inequality and the van der Waerden bound

L. Gurvits, *Van der Waerden/Schrijver–Valiant like conjectures and stable (aka hyperbolic)
homogeneous polynomials: one theorem for all*, Electron. J. Combin. 15 (2008).

For a real-stable polynomial `p` in variables `x₀, …, x_k` with nonnegative coefficients and
total degree at most `k + 1`, `step p = (∂p/∂x₀)|_{x₀ = 0}` is again real stable (or zero), and
`capacity (step p) ≥ gurvitsFactor (k + 1) * capacity p`: for positive `y`, the univariate
restriction `t ↦ p(t, y)` is real-rooted, so the univariate inequality
`mul_le_coeff_one_of_splits` applies.  Iterating over the `n` variables of
`prodLin A = ∏ i, ∑ j, A i j * x j` gives the van der Waerden bound
`per A ≥ n! / nⁿ` for doubly stochastic `A` (Egorychev–Falikman).
-/

open MvPolynomial

noncomputable section

namespace RealRooted

/-- A partial derivative of a polynomial in finitely many variables that is real stable or zero
is real stable or zero. -/
theorem MvRealStableOrZero.pderiv_of_finite {σ : Type*} [Finite σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStableOrZero P) (i : σ) : MvRealStableOrZero (pderiv i P) := by
  rcases hP with rfl | hP
  · simpa using (MvRealStableOrZero.zero (sigma := σ))
  rcases MvUpperHalfPlaneStable.pderiv_zero_or_of_finite hP i with h | h
  · left
    apply map_injective Complex.ofRealHom Complex.ofRealHom.injective
    simpa [complexifyMv, pderiv_map] using h
  · right
    simpa [MvRealStable, complexifyMv, pderiv_map] using h

namespace Gurvits

variable {n : ℕ}

/-- `step p`, with its variables renamed back into `x₁, …, xₙ`, is `∂p/∂x₀` at `x₀ = 0`. -/
theorem rename_succ_step (p : MvPolynomial (Fin (n + 1)) ℝ) :
    rename Fin.succ (step p) = specializeAt 0 0 (pderiv 0 p) := by
  classical
  unfold step specializeAt
  rw [← AlgHom.comp_apply]
  refine DFunLike.congr_fun (MvPolynomial.algHom_ext fun i => ?_) _
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- `step` preserves weak real stability. -/
theorem _root_.RealRooted.MvRealStableOrZero.step {p : MvPolynomial (Fin (n + 1)) ℝ}
    (hp : MvRealStableOrZero p) : MvRealStableOrZero (step p) := by
  refine MvRealStableOrZero.of_rename (f := Fin.succ) ?_ (Fin.succ_injective n)
  rw [rename_succ_step]
  rcases hp.pderiv_of_finite 0 with h | h
  · simpa [h] using (MvRealStableOrZero.zero (sigma := Fin (n + 1)))
  · exact h.specializeAt_zero_or_general 0 0

/-- Evaluating `p` at `(t, y)` is evaluating its univariate restriction at `t`, after
complexification. -/
theorem eval_cons_complexifyMv (p : MvPolynomial (Fin (n + 1)) ℝ) (y : Fin n → ℝ) (t : ℂ) :
    eval (Fin.cons t fun k => (y k : ℂ)) (complexifyMv p) =
      (complexify (Polynomial.map (eval y) (finSuccEquiv ℝ n p))).eval t := by
  have key : (eval (Fin.cons t fun k => (y k : ℂ))).comp (map Complex.ofRealHom) =
      (Polynomial.evalRingHom t).comp ((Polynomial.mapRingHom Complex.ofRealHom).comp
        ((Polynomial.mapRingHom (eval y)).comp (finSuccEquiv ℝ n).toRingHom)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [finSuccEquiv_apply]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  simpa [complexifyMv, complexify] using DFunLike.congr_fun key p

/-- For a weakly real-stable `p` and real `y`, the restriction `t ↦ p(t, y)` is real-rooted. -/
theorem splits_map_finSuccEquiv {p : MvPolynomial (Fin (n + 1)) ℝ}
    (hp : MvRealStableOrZero p) (y : Fin n → ℝ) :
    (Polynomial.map (eval y) (finSuccEquiv ℝ n p)).Splits := by
  classical
  set u := Polynomial.map (eval y) (finSuccEquiv ℝ n p)
  let l : List (Fin (n + 1)) := List.ofFn Fin.succ
  let c : Fin (n + 1) → ℝ := Fin.cons 0 y
  have hass (t : ℂ) : specializeAtListAssignment (fun i => (c i : ℂ)) l (fun _ => t) =
      Fin.cons t fun k => (y k : ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [specializeAtListAssignment_eq_of_not_mem _ _ (by simp [l, Fin.succ_ne_zero])]
      simp
    · rw [specializeAtListAssignment_eq_of_mem _ _ (by simp [l])]
      simp [c]
  have key (t : ℂ) :
      eval (fun _ => t) (complexifyMv (specializeAtList c l p)) = (complexify u).eval t := by
    rw [complexifyMv_specializeAtList, eval_specializeAtList, hass, eval_cons_complexifyMv]
  rcases hp.specializeAtList_general c l with h0 | hstab
  · have hu : u = 0 := by
      apply Polynomial.funext
      intro r
      have h := key r
      rw [h0, complexify, Polynomial.eval_map,
        show (r : ℂ) = Complex.ofRealHom r from rfl, Polynomial.eval₂_at_apply] at h
      rw [Polynomial.eval_zero]
      exact_mod_cast (by simpa [complexifyMv] using h.symm : ((u.eval r : ℝ) : ℂ) = 0)
    rw [hu]
    exact Polynomial.Splits.zero
  · exact IsUpperHalfPlaneStable.splits_complexify fun t ht => by
      rw [← key]
      exact hstab (fun _ => t) fun _ => ht

/-- **Gurvits' inequality.**  For a weakly real-stable `p` in `k + 1` variables with
nonnegative coefficients and total degree at most `k + 1`,
`gurvitsFactor (k + 1) * capacity p ≤ capacity (step p)`. -/
theorem gurvitsFactor_mul_capacity_le_capacity_step {k : ℕ}
    {p : MvPolynomial (Fin (k + 1)) ℝ} (hp : MvRealStableOrZero p) (hnn : ∀ m, 0 ≤ p.coeff m)
    (hdeg : p.totalDegree ≤ k + 1) :
    gurvitsFactor (k + 1) * capacity p ≤ capacity (step p) := by
  apply le_capacity
  intro y hy
  have hprod : 0 < ∏ i, y i := Finset.prod_pos fun i _ => hy i
  set u := Polynomial.map (eval y) (finSuccEquiv ℝ k p)
  have hbound : ∀ t > 0, (capacity p * ∏ i, y i) * t ≤ u.eval t := by
    intro t ht
    have hx : ∀ i, 0 < (Fin.cons t y : Fin (k + 1) → ℝ) i :=
      fun i => Fin.cases ht (fun j => hy j) i
    calc (capacity p * ∏ i, y i) * t
        = capacity p * ∏ i, (Fin.cons t y : Fin (k + 1) → ℝ) i := by
          rw [prod_fin_cons]; ring
      _ ≤ eval (Fin.cons t y) p := capacity_mul_prod_le hnn hx
      _ = u.eval t := (eval_map_finSuccEquiv p y t).symm
  have hL1 := mul_le_coeff_one_of_splits (splits_map_finSuccEquiv hp y)
    (coeff_map_finSuccEquiv_nonneg hnn fun i => (hy i).le)
    ((natDegree_map_finSuccEquiv_le p y).trans hdeg) (by lia) hbound
  rw [coeff_one_map_finSuccEquiv] at hL1
  rw [le_div_iff₀ hprod]
  calc gurvitsFactor (k + 1) * capacity p * ∏ i, y i
      = (capacity p * ∏ i, y i) * gurvitsFactor (k + 1) := by ring
    _ ≤ eval y (step p) := hL1

/-- Iterating Gurvits' inequality over all variables. -/
theorem prod_gurvitsFactor_mul_capacity_le_coeffIter :
    ∀ (k : ℕ) (p : MvPolynomial (Fin k) ℝ), MvRealStableOrZero p → (∀ m, 0 ≤ p.coeff m) →
      p.totalDegree ≤ k →
      (∏ i ∈ Finset.range k, gurvitsFactor (i + 1)) * capacity p ≤ coeffIter k p
  | 0, p, _, hnn, _ => by
    have h := capacity_le hnn (x := fun i => Fin.elim0 i) fun i => Fin.elim0 i
    simpa [coeffIter, eval_eq_coeff_zero_of_fin_zero] using h
  | k + 1, p, hs, hnn, hdeg => by
    have ih := prod_gurvitsFactor_mul_capacity_le_coeffIter k (step p) hs.step
      (coeff_step_nonneg hnn) (totalDegree_step_le hdeg)
    have hnn' : 0 ≤ ∏ i ∈ Finset.range k, gurvitsFactor (i + 1) :=
      Finset.prod_nonneg fun i _ => gurvitsFactor_nonneg _
    rw [Finset.prod_range_succ]
    calc (∏ i ∈ Finset.range k, gurvitsFactor (i + 1)) * gurvitsFactor (k + 1) * capacity p
        = (∏ i ∈ Finset.range k, gurvitsFactor (i + 1)) *
            (gurvitsFactor (k + 1) * capacity p) := by ring
      _ ≤ (∏ i ∈ Finset.range k, gurvitsFactor (i + 1)) * capacity (step p) :=
          mul_le_mul_of_nonneg_left
            (gurvitsFactor_mul_capacity_le_capacity_step hs hnn hdeg) hnn'
      _ ≤ coeffIter k (step p) := ih
      _ = coeffIter (k + 1) p := rfl

/-- **The van der Waerden conjecture** (Egorychev, Falikman; via Gurvits): the permanent of an
`n × n` doubly stochastic matrix is at least `n! / nⁿ`. -/
theorem factorial_div_pow_le_permanent {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) : (n.factorial : ℝ) / n ^ n ≤ A.permanent := by
  obtain ⟨hnn, hrow, -⟩ := mem_doublyStochastic_iff_sum.1 hA
  have hcoeff : ∀ m, 0 ≤ (prodLin A).coeff m := by
    unfold prodLin
    refine Finset.prod_induction _ (fun q : MvPolynomial (Fin n) ℝ => ∀ m, 0 ≤ q.coeff m)
      (fun a b ha hb m => ?_) (fun m => ?_) fun i _ m => ?_
    · rw [coeff_mul]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (ha _) (hb _)
    · rw [coeff_one]
      split_ifs <;> norm_num
    · rw [coeff_sum]
      refine Finset.sum_nonneg fun j _ => ?_
      rw [coeff_C_mul]
      exact mul_nonneg (hnn i j) (by rw [coeff_X]; split_ifs <;> norm_num)
  have hstab : MvRealStableOrZero (prodLin A) := by
    refine Or.inr (MvRealStable.finset_prod _ _ fun i _ => ?_)
    obtain ⟨j, hj⟩ : ∃ j, 0 < A i j := by
      by_contra h
      push Not at h
      have h0 : ∑ j, A i j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hnn i j)
      rw [hrow i] at h0
      norm_num at h0
    exact MvRealStable.finset_sum_C_mul_X Finset.univ (A i) id (fun j _ => hnn i j)
      ⟨j, by simp, hj⟩
  have hdeg : (prodLin A).totalDegree ≤ n := by
    unfold prodLin
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ i, (∑ j, C (A i j) * X j : MvPolynomial (Fin n) ℝ).totalDegree
        ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => (totalDegree_finsetSum _ _).trans
          (Finset.sup_le fun j _ => (totalDegree_mul _ _).trans (by simp))
      _ = n := by simp
  have h := prod_gurvitsFactor_mul_capacity_le_coeffIter n (prodLin A) hstab hcoeff hdeg
  rw [prod_range_gurvitsFactor, coeffIter_eq_coeff_allOnes, coeff_allOnes_prodLin] at h
  have hpos : (0 : ℝ) ≤ n.factorial / n ^ n := by positivity
  calc (n.factorial : ℝ) / n ^ n = n.factorial / n ^ n * 1 := (mul_one _).symm
    _ ≤ n.factorial / n ^ n * capacity (prodLin A) :=
        mul_le_mul_of_nonneg_left (one_le_capacity_prodLin hA) hpos
    _ ≤ A.permanent := h

end Gurvits

end RealRooted
