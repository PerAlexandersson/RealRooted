module

public import RealRooted.Gurvits.Univariate
public import RealRooted.Gurvits.Capacity
import RealRooted.MultivariateStability.Specialization
import RealRooted.MultivariateStability.LinearForm
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.Derivative
public import RealRooted.HermiteBiehler.Basic
public import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize

/-!
# Gurvits' capacity inequality and the van der Waerden bound

L. Gurvits, *Van der Waerden/Schrijver–Valiant like conjectures and stable (aka hyperbolic)
homogeneous polynomials: one theorem for all*, Electron. J. Combin. 15 (2008).

For a real-stable polynomial `p` in variables `x₀, …, x_k` with nonnegative coefficients and
degree at most `d` in `x₀`, `step p = (∂p/∂x₀)|_{x₀ = 0}` is again real stable (or zero), and
`capacity (step p) ≥ gurvitsFactor d * capacity p`: for positive `y`, the univariate
restriction `t ↦ p(t, y)` is real-rooted, so the univariate inequality
`mul_le_coeff_one_of_splits` applies.

Iterating over all variables, with a separate degree cap for each, gives Theorem 2.4 of the paper
(`prod_gurvitsFactor_min_mul_capacity_le_coeffIter`).  Applied to
`prodLin A = ∏ i, ∑ j, A i j * x j` for a nonnegative matrix `A`, this bounds `per A` below in
terms of the number of nonzero entries in each column (Corollary 2.7(a) of the paper,
`prod_gurvitsFactor_min_mul_capacity_prodLin_le_permanent`).  Using only the total degree gives
the van der Waerden bound `per A ≥ n! / nⁿ` for doubly stochastic `A` (Egorychev–Falikman).
-/

public section

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

/-- **Gurvits' inequality, degree-sensitive form.**  For a weakly real-stable `p` in `k + 1`
variables with nonnegative coefficients and degree at most `d` in `x₀`,
`gurvitsFactor d * capacity p ≤ capacity (step p)`.  This is inequality (25) of Gurvits (2008),
the inductive step of Theorem 2.4. -/
theorem gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf_le {k d : ℕ}
    {p : MvPolynomial (Fin (k + 1)) ℝ} (hp : MvRealStableOrZero p) (hnn : ∀ m, 0 ≤ p.coeff m)
    (hdeg : p.degreeOf 0 ≤ d) :
    gurvitsFactor d * capacity p ≤ capacity (step p) := by
  -- The univariate inequality needs `d ≠ 0`, and `gurvitsFactor 0 = gurvitsFactor 1`.
  wlog hd : d ≠ 0 generalizing d
  · obtain rfl : d = 0 := not_ne_iff.1 hd
    simpa using this (d := 1) (by lia) one_ne_zero
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
    ((natDegree_map_finSuccEquiv_le_degreeOf p y).trans hdeg) (by lia) hbound
  rw [coeff_one_map_finSuccEquiv] at hL1
  rw [le_div_iff₀ hprod]
  calc gurvitsFactor d * capacity p * ∏ i, y i
      = (capacity p * ∏ i, y i) * gurvitsFactor d := by ring
    _ ≤ eval y (step p) := hL1

/-- **Gurvits' inequality.**  For a weakly real-stable `p` in `k + 1` variables with
nonnegative coefficients and total degree at most `k + 1`,
`gurvitsFactor (k + 1) * capacity p ≤ capacity (step p)`. -/
theorem gurvitsFactor_mul_capacity_le_capacity_step {k : ℕ}
    {p : MvPolynomial (Fin (k + 1)) ℝ} (hp : MvRealStableOrZero p) (hnn : ∀ m, 0 ≤ p.coeff m)
    (hdeg : p.totalDegree ≤ k + 1) :
    gurvitsFactor (k + 1) * capacity p ≤ capacity (step p) :=
  gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf_le hp hnn
    ((degreeOf_le_totalDegree p 0).trans hdeg)

/-- **Gurvits' capacity inequality with a degree cap for each variable** (Gurvits 2008,
Theorem 2.4).  Let `p` be a weakly real-stable polynomial in `k` variables with nonnegative
coefficients and total degree at most `k`, with `p.degreeOf i ≤ c i` for every `i`.  Then
`(∏ i, gurvitsFactor (min (c i) (k - i))) * capacity p` is at most `coeffIter k p`, the
coefficient of `x₀ ⋯ x_{k-1}` in `p` (`coeffIter_eq_coeff_allOnes`).  The variable `x i` is
eliminated when `k - i` variables remain; the paper eliminates the variables in the opposite
order, so its index `i` corresponds to `k - i` here. -/
theorem prod_gurvitsFactor_min_mul_capacity_le_coeffIter :
    ∀ (k : ℕ) (p : MvPolynomial (Fin k) ℝ) (c : Fin k → ℕ), MvRealStableOrZero p →
      (∀ m, 0 ≤ p.coeff m) → p.totalDegree ≤ k → (∀ i, p.degreeOf i ≤ c i) →
      (∏ i : Fin k, gurvitsFactor (min (c i) (k - i))) * capacity p ≤ coeffIter k p
  | 0, p, _, _, hnn, _, _ => by
    have h := capacity_le hnn (x := fun i => Fin.elim0 i) fun i => Fin.elim0 i
    simpa [coeffIter, eval_eq_coeff_zero_of_fin_zero] using h
  | k + 1, p, c, hs, hnn, hdeg, hc => by
    have ih := prod_gurvitsFactor_min_mul_capacity_le_coeffIter k (step p) (fun i => c i.succ)
      hs.step (coeff_step_nonneg hnn) (totalDegree_step_le hdeg)
      fun i => (degreeOf_step_le p i).trans (hc i.succ)
    have hnn' : 0 ≤ ∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - i)) :=
      Finset.prod_nonneg fun i _ => gurvitsFactor_nonneg _
    have hstep := gurvitsFactor_mul_capacity_le_capacity_step_of_degreeOf_le hs hnn
      (le_min (hc 0) ((degreeOf_le_totalDegree p 0).trans hdeg))
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
    calc gurvitsFactor (min (c 0) (k + 1)) *
          (∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - i))) * capacity p
        = (∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - i))) *
            (gurvitsFactor (min (c 0) (k + 1)) * capacity p) := by ring
      _ ≤ (∏ i : Fin k, gurvitsFactor (min (c i.succ) (k - i))) * capacity (step p) :=
          mul_le_mul_of_nonneg_left hstep hnn'
      _ ≤ coeffIter k (step p) := ih
      _ = coeffIter (k + 1) p := rfl

/-- Iterating Gurvits' inequality over all variables. -/
theorem prod_gurvitsFactor_mul_capacity_le_coeffIter :
    ∀ (k : ℕ) (p : MvPolynomial (Fin k) ℝ), MvRealStableOrZero p → (∀ m, 0 ≤ p.coeff m) →
      p.totalDegree ≤ k →
      (∏ i ∈ Finset.range k, gurvitsFactor (i + 1)) * capacity p ≤ coeffIter k p := by
  intro k p hs hnn hdeg
  have h := prod_gurvitsFactor_min_mul_capacity_le_coeffIter k p (fun _ => k) hs hnn hdeg
    fun i => (degreeOf_le_totalDegree p i).trans hdeg
  have hprod : ∏ i : Fin k, gurvitsFactor (min k (k - i)) =
      ∏ i ∈ Finset.range k, gurvitsFactor (i + 1) := by
    rw [← Fin.prod_univ_eq_prod_range fun i => gurvitsFactor (i + 1)]
    refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
    rw [Fin.revPerm_apply, Fin.val_rev]
    congr 1
    lia
  rwa [hprod] at h

/-- `∏ i, ∑ j, A i j * x j` is real stable or zero for an entrywise nonnegative `A`: a row with a
positive entry gives a real-stable linear form, and a zero row makes the product zero. -/
theorem mvRealStableOrZero_prodLin {σ : Type*} [Fintype σ] {A : Matrix σ σ ℝ}
    (hA : ∀ i j, 0 ≤ A i j) : MvRealStableOrZero (prodLin A) := by
  by_cases hrow : ∀ i, ∃ j, 0 < A i j
  · refine Or.inr (MvRealStable.finset_prod _ _ fun i _ => ?_)
    obtain ⟨j, hj⟩ := hrow i
    exact MvRealStable.finset_sum_C_mul_X Finset.univ (A i) id (fun j _ => hA i j)
      ⟨j, Finset.mem_univ j, hj⟩
  · push Not at hrow
    obtain ⟨i, hi⟩ := hrow
    refine Or.inl (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    simp [fun j => le_antisymm (hi j) (hA i j)]

open scoped Finset in
/-- **Gurvits' capacity bound for the permanent of a sparse matrix** (Gurvits 2008,
Corollary 2.7(a)).  If `A` is an entrywise nonnegative `n × n` matrix and column `j` has `Δ j`
nonzero entries, then `(∏ j, gurvitsFactor (min (Δ j) (j + 1))) * capacity (prodLin A) ≤ per A`.
Columns are numbered from `0` here, so `j + 1` is the column index used in the paper. -/
theorem prod_gurvitsFactor_min_mul_capacity_prodLin_le_permanent {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    (∏ j : Fin n, gurvitsFactor (min #{i | A i j ≠ 0} ((j : ℕ) + 1))) * capacity (prodLin A) ≤
      A.permanent := by
  -- `step` eliminates `x₀` first, so reverse the columns to give column `j` the cap `j + 1`.
  have hB : ∀ i j, 0 ≤ A.submatrix id Fin.revPerm i j := fun i j => hA _ _
  have key := prod_gurvitsFactor_min_mul_capacity_le_coeffIter n
    (prodLin (A.submatrix id Fin.revPerm)) (fun v => #{i | A i (Fin.rev v) ≠ 0})
    (mvRealStableOrZero_prodLin hB) (hasNonnegCoeffs_prodLin hB)
    (by simpa using totalDegree_prodLin_le (A.submatrix id Fin.revPerm))
    (degreeOf_prodLin_le_card_filter_ne_zero _)
  rw [coeffIter_eq_coeff_allOnes, coeff_allOnes_prodLin, Matrix.permanent_permute_rows,
    capacity_prodLin_submatrix_id] at key
  refine le_of_eq_of_le (congrArg (· * capacity (prodLin A)) ?_) key
  refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
  rw [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 2
  lia

/-- **The van der Waerden conjecture** (Egorychev, Falikman; via Gurvits): the permanent of an
`n × n` doubly stochastic matrix is at least `n! / nⁿ`. -/
theorem factorial_div_pow_le_permanent {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) : (n.factorial : ℝ) / n ^ n ≤ A.permanent := by
  have hnn := (mem_doublyStochastic_iff_sum.1 hA).1
  have h := prod_gurvitsFactor_mul_capacity_le_coeffIter n (prodLin A)
    (mvRealStableOrZero_prodLin hnn) (hasNonnegCoeffs_prodLin hnn)
    (by simpa using totalDegree_prodLin_le A)
  rw [prod_range_gurvitsFactor, coeffIter_eq_coeff_allOnes, coeff_allOnes_prodLin] at h
  calc (n.factorial : ℝ) / n ^ n = n.factorial / n ^ n * 1 := (mul_one _).symm
    _ ≤ n.factorial / n ^ n * capacity (prodLin A) :=
        mul_le_mul_of_nonneg_left (one_le_capacity_prodLin hA) (by positivity)
    _ ≤ A.permanent := h

end Gurvits

end RealRooted
