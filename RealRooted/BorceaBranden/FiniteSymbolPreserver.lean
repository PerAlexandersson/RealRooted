import RealRooted.BorceaBranden.FiniteSymbolDegree
import RealRooted.BorceaBranden.FiniteSymbolProduct
import RealRooted.BorceaBranden.FiniteSymbolReconstruction
import RealRooted.BoundarySpecializationRight
import RealRooted.LiebSokalPointwise

/-!
# Finite algebraic symbols preserve stability

This module follows the proof of Borcea--Branden, arXiv:0809.0401,
Lemma 2.2: reciprocate the source block of the algebraic symbol, multiply by
the input in a third block, contract the paired source/input variables,
specialize the remaining non-target variables at zero, and reconstruct the
operator value.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- A linear operator on multiaffine polynomials preserves upper-half-plane
stability up to zero when its finite algebraic symbol is stable. Target
variables are unrestricted. This is Borcea--Branden, Lemma 2.2, specialized
to the multiaffine degree box. -/
theorem finiteSymbol_preserves_stability
    {sigma tau : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (hSymbol : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol (fun _ : sigma => 1) T))
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1))
    (hf : MvUpperHalfPlaneStable f.1) :
    MvUpperHalfPlaneStableOrZero (T f) := by
  classical
  have hSymbolDegree (i : sigma) :
      (MvPolynomial.algebraicSymbol (fun _ : sigma => 1) T).degreeOf
          (Sum.inr i) ≤ 1 :=
    MvPolynomial.degreeOf_algebraicSymbol_one_inr_le T i
  have hReciprocal : MvUpperHalfPlaneStable
      (signedMultiaffineReciprocalRight
        (MvPolynomial.algebraicSymbol (fun _ : sigma => 1) T)) :=
    hSymbol.signedMultiaffineReciprocalRight hSymbolDegree
  have hNormalized : MvUpperHalfPlaneStable
      (MvPolynomial.C ((-1 : ℂ) ^ Fintype.card sigma) *
        signedMultiaffineReciprocalRight
          (MvPolynomial.algebraicSymbol (fun _ : sigma => 1) T)) :=
    hReciprocal.C_mul (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
  have hThreeBlock : MvUpperHalfPlaneStable (paperThreeBlock T f) := by
    rw [paperThreeBlock_eq_normalizedReciprocal_mul_input]
    exact hNormalized.rename.mul hf.rename
  have hPairedDegree (i : sigma) :
      (paperThreeBlock T f).degreeOf (paperSourceEmbedding i) ≤ 1 ∧
        (paperThreeBlock T f).degreeOf (paperInputEmbedding i) ≤ 1 :=
    paperThreeBlock_paired_degree_le_one T f i
  let Q : MvPolynomial (PaperThreeBlock tau sigma) ℂ :=
    contractMappedVariablePairs paperSourceEmbedding paperInputEmbedding
      (differentialVariableOrder sigma) (paperThreeBlock T f)
  have hQStableOrZero : Q = 0 ∨ MvUpperHalfPlaneStable Q := by
    unfold Q
    apply hThreeBlock.contractMappedVariablePairs_zero_or_of_degreeOf_le_one
    intro i _hi
    exact hPairedDegree i
  have hQDegree (k : sigma ⊕ sigma) :
      Q.degreeOf (Sum.inr k) ≤ 1 := by
    unfold Q
    apply degreeOf_contractMappedVariablePairs_le_one
    rcases k with i | i
    · exact (hPairedDegree i).1
    · exact (hPairedDegree i).2
  have hQSpecialized : MvUpperHalfPlaneStableOrZero
      (specializeRight (fun _ : sigma ⊕ sigma => 0) Q) := by
    rcases hQStableOrZero with hzero | hstable
    · left
      simp [hzero]
    · exact hstable.specializeRight_zero_or_of_degreeOf_le_one hQDegree
  have hQeq :
      Q = MvPolynomial.rename paperTargetInputEmbedding
        (paperDifferentialSum T f) := by
    exact contractMappedVariablePairs_paperThreeBlock T f
  have hReconstruct :
      specializeRight (fun _ : sigma ⊕ sigma => 0) Q = T f := by
    rw [hQeq, specializeRight_zero_rename_paperTargetInputEmbedding,
      specializeRight_zero_paperDifferentialSum]
  rw [hReconstruct] at hQSpecialized
  exact hQSpecialized

end

end RealRooted.BorceaBranden
