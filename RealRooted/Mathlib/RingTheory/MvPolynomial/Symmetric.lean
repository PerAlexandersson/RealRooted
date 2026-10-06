import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Finite-variable symmetrization

This file defines permutation summation and normalized symmetrization for
multivariate polynomials. These are the algebraic operators used in the
Grace--Walsh--Szegő symmetrization argument.
-/

open BigOperators

namespace MvPolynomial

/-- The finite indexing type of permutations induced by a finite type. -/
noncomputable local instance {σ : Type*} [Fintype σ] :
    Fintype (Equiv.Perm σ) :=
  Fintype.ofFinite _

/-- Renaming every variable in an elementary symmetric polynomial to one
variable gives the corresponding binomial multiple of its power. -/
theorem rename_esymm_const
    {R sigma tau : Type*} [CommSemiring R] [Fintype sigma] (r : ℕ) (v : tau) :
    rename (fun _ : sigma => v) (esymm sigma R r) =
      Nat.choose (Fintype.card sigma) r • X v ^ r := by
  rw [esymm]
  simp only [map_sum, map_prod, rename_X]
  calc
    ∑ t ∈ Finset.univ.powersetCard r,
        ∏ _x ∈ t, X v =
      ∑ _t ∈ Finset.univ.powersetCard r, X v ^ r := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ]

/-- A symmetric polynomial of degree at most one in each variable is a linear
combination of elementary symmetric polynomials. The coefficient of `esymm k`
is the coefficient of the staircase monomial `X 0 * ⋯ * X (k - 1)`. -/
theorem IsSymmetric.eq_sum_C_mul_esymm {R : Type*} [CommRing R] {n : ℕ}
    {P : MvPolynomial (Fin n) R} (hs : P.IsSymmetric) (hma : ∀ i, P.degreeOf i ≤ 1) :
    P = ∑ k ∈ Finset.range (n + 1),
      MvPolynomial.C (P.coeff (∑ i : Fin n, if (i : ℕ) < k then Finsupp.single i 1 else 0)) *
        esymm (Fin n) R k := by
  classical
  have ind_apply : ∀ (s : Finset (Fin n)) j,
      (∑ i ∈ s, Finsupp.single i 1 : Fin n →₀ ℕ) j = if j ∈ s then 1 else 0 := by
    intro s j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  have ind_inj : ∀ s t : Finset (Fin n),
      (∑ i ∈ s, Finsupp.single i 1 : Fin n →₀ ℕ) = ∑ i ∈ t, Finsupp.single i 1 ↔ s = t := by
    refine fun s t => ⟨fun h => ?_, fun h => h ▸ rfl⟩
    ext j
    have := congrArg (· j) h
    simp only [ind_apply] at this
    split_ifs at this <;> simp_all
  have symm : ∀ s t : Finset (Fin n), s.card = t.card →
      P.coeff (∑ i ∈ s, Finsupp.single i 1) = P.coeff (∑ i ∈ t, Finsupp.single i 1) := by
    intro s t hst
    let e : {x // x ∈ s} ≃ {x // x ∈ t} := Fintype.equivOfCardEq (by simpa using hst)
    let σ : Equiv.Perm (Fin n) := Equiv.extendSubtype e
    have key := coeff_rename_mapDomain σ σ.injective P (∑ i ∈ s, Finsupp.single i 1)
    rw [hs σ] at key
    rw [← key]
    congr 1
    ext j
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [Finsupp.mapDomain_apply_of_injective σ.injective, ind_apply, ind_apply]
    by_cases hj : j ∈ s
    · simp [hj, σ, Equiv.extendSubtype_mem e j hj]
    · simp [hj, σ, Equiv.extendSubtype_not_mem e j hj]
  ext m
  simp only [coeff_sum, coeff_C_mul, esymm_eq_sum_monomial, coeff_monomial]
  by_cases hm : ∀ i, m i ≤ 1
  · set t := Finset.univ.filter (fun i => m i = 1)
    have hmt : m = ∑ i ∈ t, Finsupp.single i 1 := by
      ext j
      rw [ind_apply]
      have := hm j
      by_cases h : m j = 1
      · simp [t, h]
      · simp only [t, Finset.mem_filter, Finset.mem_univ, h, and_false, ite_false]
        lia
    have htn : t.card ≤ n := by simpa using Finset.card_le_univ t
    simp_rw [hmt, ind_inj, Finset.sum_ite_eq', Finset.mem_powersetCard, Finset.subset_univ,
      true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
      Nat.lt_succ_of_le htn, ite_true]
    rw [← Finset.sum_filter]
    apply symm
    rw [Fin.card_filter_val_lt, min_eq_right htn]
  · push Not at hm
    obtain ⟨i, hi⟩ := hm
    rw [notMem_support_iff.1 fun (h : m ∈ P.support) =>
      absurd (monomial_le_degreeOf i h) (by have := hma i; lia)]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s _ => ?_)
    rw [ite_eq_right_iff]
    rintro rfl
    rw [ind_apply] at hi
    split_ifs at hi <;> lia

/-- Sum all variable permutations of a multivariate polynomial. -/
noncomputable def symmetrizationSum
    {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact ∑ e : Equiv.Perm σ, rename e p

/-- The permutation sum is symmetric. -/
theorem symmetrizationSum_isSymmetric
    {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) :
    IsSymmetric (symmetrizationSum p) := by
  classical
  intro e
  simp only [symmetrizationSum, map_sum, rename_rename]
  simpa [Function.comp_def] using
    Equiv.sum_comp (Equiv.mulLeft e)
      (fun f : Equiv.Perm σ => rename f p)

/-- Average all variable permutations of a complex multivariate polynomial. -/
noncomputable def fullSymmetrization
    {σ R : Type*} [Fintype σ] [Field R] [CharZero R]
    (p : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact C (Fintype.card (Equiv.Perm σ) : R)⁻¹ *
    symmetrizationSum p

/-- Full symmetrization is symmetric. -/
theorem fullSymmetrization_isSymmetric
    {σ R : Type*} [Fintype σ] [Field R] [CharZero R]
    (p : MvPolynomial σ R) :
    IsSymmetric (fullSymmetrization p) := by
  classical
  intro e
  simp only [fullSymmetrization, map_mul, rename_C]
  rw [symmetrizationSum_isSymmetric p e]

/-- Full symmetrization preserves evaluation at a constant assignment. -/
theorem eval_fullSymmetrization_const
    {σ R : Type*} [Fintype σ] [Field R] [CharZero R]
    (p : MvPolynomial σ R) (w : R) :
    eval (fun _ : σ => w) (fullSymmetrization p) =
      eval (fun _ : σ => w) p := by
  classical
  have hcard : (Fintype.card (Equiv.Perm σ) : R) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hconst (e : Equiv.Perm σ) :
      (fun _ : σ => w) ∘ e = fun _ : σ => w := by
    rfl
  simp only [fullSymmetrization, map_mul, eval_C,
    symmetrizationSum, map_sum, eval_rename, hconst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end MvPolynomial

namespace MvPolynomial

/-- Convex-form partial symmetrization associated with a permutation. -/
noncomputable def partialSymmetrization
    {σ R : Type*} [CommRing R]
    (t : R) (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    MvPolynomial σ R :=
  C t * p + C (1 - t) * rename e p

/-- At weight zero, partial symmetrization is variable permutation. -/
@[simp] theorem partialSymmetrization_zero
    {σ R : Type*} [CommRing R]
    (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    partialSymmetrization 0 e p = rename e p := by
  simp [partialSymmetrization]

/-- At weight one, partial symmetrization is the original polynomial. -/
@[simp] theorem partialSymmetrization_one
    {σ R : Type*} [CommRing R]
    (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    partialSymmetrization 1 e p = p := by
  simp [partialSymmetrization]

/-- Partial symmetrization preserves evaluation at a constant assignment. -/
theorem eval_partialSymmetrization_const
    {σ R : Type*} [CommRing R]
    (t w : R) (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    eval (fun _ : σ => w) (partialSymmetrization t e p) =
      eval (fun _ : σ => w) p := by
  have hconst : (fun _ : σ => w) ∘ e = fun _ : σ => w := by rfl
  simp only [partialSymmetrization, map_add, map_mul, eval_C,
    eval_rename, hconst]
  ring

end MvPolynomial
