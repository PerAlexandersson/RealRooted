import RealRooted.BorceaBranden.FiniteSymbolContraction
import RealRooted.BorceaBranden.FiniteSymbolReciprocal

/-!
# The three-block product in the finite-symbol argument

This module identifies the reciprocal-symbol product in Borcea--Branden,
arXiv:0809.0401, Lemma 2.2, with the three-block contraction sum and proves
the source/input degree bounds needed for the repeated Lieb--Sokal step.
Target variables remain unrestricted.
-/

open BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

/-- The signed squarefree basis monomial becomes the product `(-X_i) ^ m_i`
after renaming. -/
private theorem rename_signedBasisMonomial_eq_prod
    {sigma omega : Type*} [Fintype sigma]
    (e : sigma → omega) (m : OneBox sigma) :
    MvPolynomial.rename e (signedBasisMonomial m) =
      ∏ i : sigma, (-MvPolynomial.X (e i)) ^ m.1 i := by
  classical
  have hmonomial :
      MvPolynomial.monomial m.1
          ((-1 : ℂ) ^ (m.1.sum fun _ n => n)) =
        MvPolynomial.C ((-1 : ℂ) ^ (m.1.sum fun _ n => n)) *
          MvPolynomial.monomial m.1 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [signedBasisMonomial, hmonomial, map_mul,
    MvPolynomial.rename_C, ← MvPolynomial.prod_X_pow_eq_monomial]
  simp only [map_prod, map_pow, MvPolynomial.rename_X]
  have hneg (i : sigma) :
      (-MvPolynomial.X (e i)) ^ m.1 i =
        MvPolynomial.C (-1 : ℂ) ^ m.1 i *
          MvPolynomial.X (e i) ^ m.1 i := by
    rw [show -MvPolynomial.X (e i) =
      MvPolynomial.C (-1 : ℂ) * MvPolynomial.X (e i) by simp, mul_pow]
  simp_rw [hneg]
  rw [Finset.prod_mul_distrib]
  simp only [← map_pow, ← map_prod]
  rw [Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  apply congrArg₂ (· * ·)
  · congr 1
    apply Finset.prod_subset (Finset.subset_univ m.1.support)
    intro i _hi hiSupport
    simp [Finsupp.notMem_support_iff.mp hiSupport]
  · apply Finset.prod_subset (Finset.subset_univ m.1.support)
    intro i _hi hiSupport
    simp [Finsupp.notMem_support_iff.mp hiSupport]

/-- The stable reciprocal-symbol product is exactly the three-block polynomial
used in the contraction calculation of Borcea--Branden, Lemma 2.2. -/
theorem paperThreeBlock_eq_normalizedReciprocal_mul_input
    {sigma tau : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1)) :
    paperThreeBlock T f =
      MvPolynomial.rename
          (Sum.elim paperTargetEmbedding paperSourceEmbedding)
          (MvPolynomial.C ((-1 : ℂ) ^ Fintype.card sigma) *
            signedMultiaffineReciprocalRight
              (MvPolynomial.algebraicSymbol (fun _ : sigma => 1) T)) *
        MvPolynomial.rename paperInputEmbedding f.1 := by
  classical
  rw [paperNormalized_signedMultiaffineReciprocalRight_algebraicSymbol_one]
  rw [map_sum, Finset.sum_mul, paperThreeBlock]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [map_mul]
  simp only [map_prod, map_pow, map_neg, MvPolynomial.rename_X,
    MvPolynomial.rename_rename, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr]
  rw [← rename_signedBasisMonomial_eq_prod paperSourceEmbedding m]
  simp only [pairedProduct, map_mul, MvPolynomial.rename_rename,
    Function.comp_def]
  ring

private theorem signedBasisMonomial_isMultiaffine
    {sigma : Type*} (m : OneBox sigma) :
    MvPolynomial.IsMultiaffine (signedBasisMonomial m) := by
  intro i
  rw [signedBasisMonomial,
    MvPolynomial.degreeOf_monomial_eq m.1 i
      (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))]
  exact m.2 i

private theorem degreeOf_rename_paperTargetEmbedding_eq_zero
    {sigma tau : Type*} (A : MvPolynomial tau ℂ) (k : sigma ⊕ sigma) :
    (MvPolynomial.rename paperTargetEmbedding A).degreeOf (Sum.inr k) = 0 := by
  classical
  apply not_ne_iff.mp
  apply (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).not.mp
  intro h
  obtain ⟨j, _hj, hji⟩ :=
    MvPolynomial.mem_vars_rename paperTargetEmbedding A h
  exact Sum.inl_ne_inr hji

private theorem paperThreeBlock_degreeOf_nonTarget_le_one
    {sigma tau : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1))
    (k : sigma ⊕ sigma) :
    (paperThreeBlock T f).degreeOf (Sum.inr k) ≤ 1 := by
  classical
  rw [paperThreeBlock]
  refine (MvPolynomial.degreeOf_sum_le (Sum.inr k) Finset.univ
    (fun m : OneBox sigma =>
      MvPolynomial.rename paperTargetEmbedding
          (T (MvPolynomial.basisDegreeOfLE
            (R := ℂ) (fun _ : sigma => 1) m)) *
        MvPolynomial.rename Sum.inr
          (pairedProduct (signedBasisMonomial m) f.1))).trans ?_
  apply Finset.sup_le
  intro m _hm
  refine (MvPolynomial.degreeOf_mul_le (Sum.inr k)
    (MvPolynomial.rename paperTargetEmbedding
      (T (MvPolynomial.basisDegreeOfLE
        (R := ℂ) (fun _ : sigma => 1) m)))
    (MvPolynomial.rename Sum.inr
      (pairedProduct (signedBasisMonomial m) f.1))).trans ?_
  rw [degreeOf_rename_paperTargetEmbedding_eq_zero, zero_add]
  have hf : MvPolynomial.IsMultiaffine f.1 :=
    (MvPolynomial.mem_degreeOfLE_iff_degreeOf f.1).mp f.2
  exact ((isMultiaffine_pairedProduct
    (signedBasisMonomial_isMultiaffine m) hf).rename Sum.inr_injective)
      (Sum.inr k)

/-- The source and input coordinates paired by the paper's contractions are
affine. No condition is imposed on target-coordinate degrees. -/
theorem paperThreeBlock_paired_degree_le_one
    {sigma tau : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1))
    (i : sigma) :
    (paperThreeBlock T f).degreeOf (paperSourceEmbedding i) ≤ 1 ∧
      (paperThreeBlock T f).degreeOf (paperInputEmbedding i) ≤ 1 :=
  ⟨paperThreeBlock_degreeOf_nonTarget_le_one T f (Sum.inl i),
    paperThreeBlock_degreeOf_nonTarget_le_one T f (Sum.inr i)⟩

end

end RealRooted.BorceaBranden
