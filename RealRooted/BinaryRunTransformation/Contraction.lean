import RealRooted.BinaryRunTransformation.Deformation
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
import RealRooted.BorceaBranden.FiniteSymbolContraction
import RealRooted.BorceaBranden.FiniteSymbolReconstructionCore
import RealRooted.BoundarySpecializationRight
import RealRooted.ElementaryDifferential
import RealRooted.LiebSokalPointwise

/-!
# Normalized diagonal contraction

This file constructs the stability-preserving contraction that sends the
coefficient of `S^k T^k` to `(-1)^k / choose n k` times that coefficient.
The construction first polarizes the two source variables into `n` clones,
contracts corresponding clone pairs, and finally specializes every remaining
clone to zero.  Output variables are passive spectators throughout.
-/

namespace RealRooted

noncomputable section

open BorceaBranden

/-- The two `n`-element clone blocks used for normalized diagonal
contraction. -/
abbrev BinaryRunPolarizedSource (n : ℕ) :=
  PolarizedSource (fun _ : Fin 2 => n)

/-- Identify the two clone blocks with the canonical sum used by paired
Lieb--Sokal contraction. -/
def binaryRunSourceEquiv (n : ℕ) :
    BinaryRunPolarizedSource n ≃ Fin n ⊕ Fin n where
  toFun x := Fin.cases (Sum.inl x.2) (fun _ => Sum.inr x.2) x.1
  invFun x := match x with
    | Sum.inl j => ⟨0, j⟩
    | Sum.inr j => ⟨1, j⟩
  left_inv x := by
    rcases x with ⟨i, j⟩
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with j | j <;> rfl

/-- Source-block polarization, expressed in the canonical target/left/right
ambient variable type. -/
def binaryRunSourcePolarization {τ : Type*} [Fintype τ] (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 2) ℂ) :
    MvPolynomial (BorceaBranden.PaperThreeBlock τ (Fin n)) ℂ :=
  MvPolynomial.rename
    (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
    (sourceBlockwisePolarizationGeneral (fun _ : Fin 2 => n) P)

theorem degreeOf_binaryRunSourcePolarization_source_le_one
    {τ : Type*} [Fintype τ] (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 2) ℂ) (j : Fin n) :
    (binaryRunSourcePolarization n P).degreeOf
        (BorceaBranden.paperSourceEmbedding j) ≤ 1 := by
  change (MvPolynomial.rename
    (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
      (sourceBlockwisePolarizationGeneral (fun _ : Fin 2 => n) P)).degreeOf
        ((Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
          (Sum.inr ⟨0, j⟩)) ≤ 1
  rw [
    MvPolynomial.degreeOf_rename_of_injective
      (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n)).injective]
  exact degreeOf_sourceBlockwisePolarizationGeneral_inr_le_one
    (fun _ : Fin 2 => n) P ⟨0, j⟩

theorem degreeOf_binaryRunSourcePolarization_input_le_one
    {τ : Type*} [Fintype τ] (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 2) ℂ) (j : Fin n) :
    (binaryRunSourcePolarization n P).degreeOf
        (BorceaBranden.paperInputEmbedding j) ≤ 1 := by
  change (MvPolynomial.rename
    (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
      (sourceBlockwisePolarizationGeneral (fun _ : Fin 2 => n) P)).degreeOf
        ((Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
          (Sum.inr ⟨1, j⟩)) ≤ 1
  rw [
    MvPolynomial.degreeOf_rename_of_injective
      (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n)).injective]
  exact degreeOf_sourceBlockwisePolarizationGeneral_inr_le_one
    (fun _ : Fin 2 => n) P ⟨1, j⟩

theorem degreeOf_binaryRunSourcePolarization_inr_le_one
    {τ : Type*} [Fintype τ] (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 2) ℂ) (x : Fin n ⊕ Fin n) :
    (binaryRunSourcePolarization n P).degreeOf (Sum.inr x) ≤ 1 := by
  rcases x with j | j
  · exact degreeOf_binaryRunSourcePolarization_source_le_one n P j
  · exact degreeOf_binaryRunSourcePolarization_input_le_one n P j

theorem rename_blockElementarySymmetric_binaryRunSourceEquiv
    (n : ℕ) (a : Fin 2 →₀ ℕ) :
    MvPolynomial.rename (binaryRunSourceEquiv n)
        (blockElementarySymmetric (fun _ : Fin 2 => n) a) =
      pairedProduct (MvPolynomial.esymm (Fin n) ℂ (a 0))
        (MvPolynomial.esymm (Fin n) ℂ (a 1)) := by
  classical
  unfold blockElementarySymmetric pairedProduct
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by rfl,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [map_mul, MvPolynomial.rename_rename]
  congr 1

theorem eval_zero_applyNegDifferential_esymm (n i j : ℕ) :
    MvPolynomial.eval (fun _ : Fin n => 0)
        (applyNegDifferential (MvPolynomial.esymm (Fin n) ℂ i)
          (MvPolynomial.esymm (Fin n) ℂ j)) =
      if i = j then (-1 : ℂ) ^ i * Nat.choose n i else 0 := by
  rw [applyNegDifferential_esymm]
  by_cases hij : i ≤ j
  · rw [ite_eq_left hij]
    by_cases heq : i = j
    · subst j
      simp
    · rw [ite_eq_right heq]
      have hpos : 0 < j - i := by lia
      rw [map_mul, MvPolynomial.eval_C, map_nsmul]
      change (-1 : ℂ) ^ i *
        ((Fintype.card (Fin n) + i - j).choose i •
          MvPolynomial.aeval (fun _ : Fin n => (0 : ℂ))
            (MvPolynomial.esymm (Fin n) ℂ (j - i))) = 0
      rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
      have hzero : (Multiset.replicate n (0 : ℂ)).esymm (j - i) = 0 := by
        have hscale := Multiset.pow_smul_esymm (R := ℂ) (0 : ℂ)
          (j - i) (Multiset.replicate n (1 : ℂ))
        simpa [zero_pow hpos.ne'] using hscale.symm
      simp [hzero]
  · rw [ite_eq_right hij, ite_eq_right (fun h => hij h.le)]
    simp

private theorem normalizedDiagonalContraction_polarizedTerm
    {τ : Type*} (n : ℕ) (A : MvPolynomial τ ℂ)
    (a : Fin 2 →₀ ℕ) (c : ℂ) :
    specializeRight (fun _ : Fin n ⊕ Fin n => 0)
        (contractMappedVariablePairs BorceaBranden.paperSourceEmbedding
          BorceaBranden.paperInputEmbedding
          (differentialVariableOrder (Fin n))
          (MvPolynomial.rename
            (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
            (MvPolynomial.C c * MvPolynomial.rename Sum.inl A *
              MvPolynomial.rename Sum.inr
                (blockElementarySymmetric (fun _ : Fin 2 => n) a)))) =
      if a 0 = a 1 then
        MvPolynomial.C (c * ((-1 : ℂ) ^ (a 0) * Nat.choose n (a 0))) * A
      else 0 := by
  classical
  have hrename :
      MvPolynomial.rename
          (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
          (MvPolynomial.C c * MvPolynomial.rename Sum.inl A *
            MvPolynomial.rename Sum.inr
              (blockElementarySymmetric (fun _ : Fin 2 => n) a)) =
        MvPolynomial.rename BorceaBranden.paperTargetEmbedding
            (MvPolynomial.C c * A) *
          MvPolynomial.rename Sum.inr
            (pairedProduct (MvPolynomial.esymm (Fin n) ℂ (a 0))
              (MvPolynomial.esymm (Fin n) ℂ (a 1))) := by
    simp only [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_rename]
    change MvPolynomial.C c *
        MvPolynomial.rename BorceaBranden.paperTargetEmbedding A *
          MvPolynomial.rename (Sum.inr ∘ binaryRunSourceEquiv n)
            (blockElementarySymmetric (fun _ : Fin 2 => n) a) = _
    rw [← MvPolynomial.rename_rename,
      rename_blockElementarySymmetric_binaryRunSourceEquiv]
  rw [hrename,
    BorceaBranden.contractMappedVariablePairs_targetMul_rename,
    contractVariablePairs_pairedProduct _ _
      (MvPolynomial.IsMultiaffine.esymm (a 0))]
  have hlift :
      MvPolynomial.rename BorceaBranden.paperTargetEmbedding
          (MvPolynomial.C c * A) *
        MvPolynomial.rename Sum.inr
          (MvPolynomial.rename Sum.inr
            (applyNegDifferential (MvPolynomial.esymm (Fin n) ℂ (a 0))
              (MvPolynomial.esymm (Fin n) ℂ (a 1)))) =
      MvPolynomial.rename BorceaBranden.paperTargetInputEmbedding
        (MvPolynomial.rename Sum.inl (MvPolynomial.C c * A) *
          MvPolynomial.rename Sum.inr
            (applyNegDifferential (MvPolynomial.esymm (Fin n) ℂ (a 0))
              (MvPolynomial.esymm (Fin n) ℂ (a 1)))) := by
    simp [BorceaBranden.paperTargetInputEmbedding,
      BorceaBranden.paperTargetEmbedding, Function.comp_def]
  rw [hlift,
    BorceaBranden.specializeRight_zero_rename_paperTargetInputEmbedding,
    BorceaBranden.specializeRight_zero_targetMul_input,
    eval_zero_applyNegDifferential_esymm]
  by_cases h : a 0 = a 1
  · simp only [h, ↓reduceIte]
    rw [mul_comm (MvPolynomial.C c) A, mul_assoc,
      ← MvPolynomial.C_mul]
    exact mul_comm _ _
  · simp [h]

/-- Polarize two source variables, contract corresponding clone pairs, and
set every remaining clone variable to zero. -/
def normalizedDiagonalContraction {τ : Type*} [Fintype τ] (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 2) ℂ) : MvPolynomial τ ℂ :=
  specializeRight (fun _ : Fin n ⊕ Fin n => 0) <|
    contractMappedVariablePairs BorceaBranden.paperSourceEmbedding
      BorceaBranden.paperInputEmbedding (differentialVariableOrder (Fin n)) <|
        binaryRunSourcePolarization n P

/-- Exact expansion of the contraction before reducing the surviving diagonal
indices. -/
theorem normalizedDiagonalContraction_eq_box_sum
    {τ : Type*} [Fintype τ] (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 2) ℂ) :
    normalizedDiagonalContraction n P =
      ∑ a : {a : Fin 2 →₀ ℕ // ∀ i, a i ≤ n},
        if a.1 0 = a.1 1 then
          MvPolynomial.C
              ((MvPolynomial.boxChoose (fun _ : Fin 2 => n) a.1 : ℂ)⁻¹ *
                ((-1 : ℂ) ^ (a.1 0) * Nat.choose n (a.1 0))) *
            sourceCoefficientGeneral P a.1
        else 0 := by
  classical
  unfold normalizedDiagonalContraction binaryRunSourcePolarization
  unfold sourceBlockwisePolarizationGeneral
  rw [map_sum]
  change specializeRight (fun _ : Fin n ⊕ Fin n => 0)
      (contractMappedVariablePairs BorceaBranden.paperSourceEmbedding
        BorceaBranden.paperInputEmbedding (differentialVariableOrder (Fin n))
        (∑ a : {a : Fin 2 →₀ ℕ // ∀ i, a i ≤ n},
          MvPolynomial.rename
            (Equiv.sumCongr (Equiv.refl τ) (binaryRunSourceEquiv n))
            (MvPolynomial.C
                ((MvPolynomial.boxChoose (fun _ : Fin 2 => n) a.1 : ℂ)⁻¹) *
              MvPolynomial.rename Sum.inl (sourceCoefficientGeneral P a.1) *
                MvPolynomial.rename Sum.inr
                  (blockElementarySymmetric
                    (fun _ : Fin 2 => n) a.1)))) = _
  rw [contractMappedVariablePairs_sum]
  unfold specializeRight
  rw [map_sum]
  apply Fintype.sum_congr
  intro a
  exact normalizedDiagonalContraction_polarizedTerm n
    (sourceCoefficientGeneral P a.1) a.1
      ((MvPolynomial.boxChoose (fun _ : Fin 2 => n) a.1 : ℂ)⁻¹)

/-- The normalized diagonal contraction preserves upper-half-plane stability,
up to the zero polynomial. -/
theorem mvUpperHalfPlaneStableOrZero_normalizedDiagonalContraction
    {τ : Type*} [Fintype τ] (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 2) ℂ)
    (hdegree : ∀ i, P.degreeOf (Sum.inr i) ≤ n)
    (hstable : MvUpperHalfPlaneStable P) :
    MvUpperHalfPlaneStableOrZero (normalizedDiagonalContraction n P) := by
  let Ppolar := binaryRunSourcePolarization n P
  have hpolar : MvUpperHalfPlaneStable Ppolar :=
    (mvUpperHalfPlaneStable_sourceBlockwisePolarizationGeneral
      (fun _ : Fin 2 => n) P hdegree hstable).rename
  let Q := contractMappedVariablePairs BorceaBranden.paperSourceEmbedding
    BorceaBranden.paperInputEmbedding
      (differentialVariableOrder (Fin n)) Ppolar
  have hQ : Q = 0 ∨ MvUpperHalfPlaneStable Q := by
    apply hpolar.contractMappedVariablePairs_zero_or_of_degreeOf_le_one
    intro j _hj
    exact ⟨degreeOf_binaryRunSourcePolarization_source_le_one n P j,
      degreeOf_binaryRunSourcePolarization_input_le_one n P j⟩
  have hQdegree (x : Fin n ⊕ Fin n) :
      Q.degreeOf (Sum.inr x) ≤ 1 := by
    refine (degreeOf_contractMappedVariablePairs_le
      BorceaBranden.paperSourceEmbedding BorceaBranden.paperInputEmbedding
      (differentialVariableOrder (Fin n)) Ppolar (Sum.inr x)).trans
        ?_
    exact degreeOf_binaryRunSourcePolarization_inr_le_one n P x
  change MvUpperHalfPlaneStableOrZero
    (specializeRight (fun _ : Fin n ⊕ Fin n => 0) Q)
  rcases hQ with hzero | hstableQ
  · left
    simp [hzero, specializeRight]
  · exact hstableQ.specializeRight_zero_or_of_degreeOf_le_one hQdegree

/-- The normalized contraction also preserves the zero-aware form of
upper-half-plane stability. -/
theorem MvUpperHalfPlaneStableOrZero.normalizedDiagonalContraction
    {τ : Type*} [Fintype τ] {n : ℕ}
    {P : MvPolynomial (τ ⊕ Fin 2) ℂ}
    (hstable : MvUpperHalfPlaneStableOrZero P)
    (hdegree : ∀ i, P.degreeOf (Sum.inr i) ≤ n) :
    MvUpperHalfPlaneStableOrZero (normalizedDiagonalContraction n P) := by
  rcases hstable with rfl | hstable
  · left
    rw [normalizedDiagonalContraction_eq_box_sum]
    simp [sourceCoefficientGeneral]
  · exact mvUpperHalfPlaneStableOrZero_normalizedDiagonalContraction
      n P hdegree hstable

end

end RealRooted
