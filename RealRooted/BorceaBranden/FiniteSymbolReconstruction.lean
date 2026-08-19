import RealRooted.BorceaBranden.FiniteSymbolContraction
import RealRooted.BorceaBranden.FiniteSymbolReconstructionCore

/-!
# Reconstruction for the finite-symbol argument

This module completes the algebraic reconstruction step in Borcea--Branden,
arXiv:0809.0401, Lemma 2.2. Target variables remain unrestricted throughout.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- Specializing the source and input coordinates of the three-block embedding
at zero is the same as specializing the actual input block at zero. -/
theorem specializeRight_zero_rename_paperTargetInputEmbedding
    {sigma tau : Type*} (D : MvPolynomial (tau ⊕ sigma) ℂ) :
    specializeRight (fun _ : sigma ⊕ sigma => 0)
        (MvPolynomial.rename paperTargetInputEmbedding D) =
      specializeRight (fun _ : sigma => 0) D := by
  classical
  unfold specializeRight
  rw [MvPolynomial.aeval_rename]
  apply congrArg
    (fun g : tau ⊕ sigma → MvPolynomial tau ℂ =>
      MvPolynomial.aeval g D)
  funext i
  cases i <;>
    simp [paperTargetInputEmbedding, paperTargetEmbedding,
      paperInputEmbedding, Function.comp_def]

/-- The derivative-at-zero sum in Borcea--Branden, Lemma 2.2 reconstructs
the value of the linear operator on its multiaffine input. -/
theorem specializeRight_zero_paperDifferentialSum
    {sigma tau : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1)) :
    specializeRight (fun _ : sigma => 0) (paperDifferentialSum T f) =
      T f := by
  classical
  rw [paperDifferentialSum]
  unfold specializeRight
  rw [map_sum]
  change
    (∑ m : OneBox sigma,
      specializeRight (fun _ : sigma => 0)
        (MvPolynomial.rename Sum.inl
            (T (MvPolynomial.basisDegreeOfLE
              (R := ℂ) (fun _ : sigma => 1) m)) *
          MvPolynomial.rename Sum.inr
            (applyMonomialDifferential m.1 f.1))) = T f
  simp_rw [specializeRight_zero_targetMul_input,
    eval_zero_applyMonomialDifferential_oneBox]
  calc
    ∑ m : OneBox sigma,
        T (MvPolynomial.basisDegreeOfLE
            (R := ℂ) (fun _ : sigma => 1) m) *
          MvPolynomial.C (MvPolynomial.coeff m.1 f.1) =
      ∑ m : OneBox sigma,
        ((MvPolynomial.basisDegreeOfLE (R := ℂ)
            (fun _ : sigma => 1)).repr f m) •
          T (MvPolynomial.basisDegreeOfLE
            (R := ℂ) (fun _ : sigma => 1) m) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [MvPolynomial.basisDegreeOfLE_repr_apply,
        MvPolynomial.smul_eq_C_mul]
      exact mul_comm _ _
    _ = T
        (∑ m : OneBox sigma,
          ((MvPolynomial.basisDegreeOfLE (R := ℂ)
              (fun _ : sigma => 1)).repr f m) •
            MvPolynomial.basisDegreeOfLE
              (R := ℂ) (fun _ : sigma => 1) m) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [map_smul]
    _ = T f := by rw [Module.Basis.sum_repr]

end

end RealRooted.BorceaBranden
