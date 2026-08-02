import RealRooted.BorceaBranden.FiniteSymbolBasis
import RealRooted.LiebSokalOperator
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.DegreeBox

/-!
# The contraction calculation for finite algebraic symbols

This file formalizes the repeated Lieb--Sokal calculation in the proof of
Borcea--Branden, arXiv:0809.0401, Lemma 2.2.  The target variables are passive
spectators: only the source/input pairs are contracted, and no finiteness or
degree condition is imposed on the target variable type.
-/

open BigOperators

namespace RealRooted

noncomputable section

/-- Iterated mapped contraction is additive in the polynomial argument. -/
theorem contractMappedVariablePairs_add
    {R sigma omega : Type*} [CommRing R]
    (left right : sigma → omega) (l : List sigma)
    (P Q : MvPolynomial omega R) :
    contractMappedVariablePairs left right l (P + Q) =
      contractMappedVariablePairs left right l P +
        contractMappedVariablePairs left right l Q := by
  induction l generalizing P Q with
  | nil => rfl
  | cons i l ih =>
      rw [contractMappedVariablePairs_cons, contractVariables_add, ih,
        contractMappedVariablePairs_cons, contractMappedVariablePairs_cons]

/-- Iterated mapped contraction commutes with finite sums. -/
theorem contractMappedVariablePairs_sum
    {R sigma omega ι : Type*} [CommRing R]
    (left right : sigma → omega) (l : List sigma)
    (s : Finset ι) (P : ι → MvPolynomial omega R) :
    contractMappedVariablePairs left right l (∑ i ∈ s, P i) =
      ∑ i ∈ s, contractMappedVariablePairs left right l (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [contractMappedVariablePairs_add, ih]

namespace BorceaBranden

/-- Exponent vectors indexing the squarefree monomial basis. -/
abbrev OneBox (sigma : Type*) :=
  {m : sigma →₀ ℕ // ∀ i, m i ≤ 1}

/-- The monomial `(-w)^m` appearing after the paper's signed reciprocal. -/
def signedBasisMonomial
    {sigma : Type*} (m : OneBox sigma) : MvPolynomial sigma ℂ :=
  MvPolynomial.monomial m.1
    ((-1 : ℂ) ^ (m.1.sum fun _ n => n))

/-- The ambient target/source/input variable type used in Lemma 2.2. -/
abbrev PaperThreeBlock (tau sigma : Type*) := tau ⊕ (sigma ⊕ sigma)

/-- Embed the unrestricted target variables into the three-block ambient type. -/
abbrev paperTargetEmbedding {tau sigma : Type*} :
    tau → PaperThreeBlock tau sigma :=
  Sum.inl

/-- Embed the source-symbol variables into the three-block ambient type. -/
abbrev paperSourceEmbedding {tau sigma : Type*} :
    sigma → PaperThreeBlock tau sigma :=
  fun i => Sum.inr (Sum.inl i)

/-- Embed the input variables into the three-block ambient type. -/
abbrev paperInputEmbedding {tau sigma : Type*} :
    sigma → PaperThreeBlock tau sigma :=
  fun i => Sum.inr (Sum.inr i)

/-- Embed the target/input block after all source variables are contracted. -/
abbrev paperTargetInputEmbedding {tau sigma : Type*} :
    tau ⊕ sigma → PaperThreeBlock tau sigma :=
  Sum.elim paperTargetEmbedding paperInputEmbedding

private theorem source_notMem_targetVars
    {R tau sigma : Type*} [CommRing R]
    (i : sigma) (A : MvPolynomial tau R) :
    (Sum.inr (Sum.inl i) : PaperThreeBlock tau sigma) ∉
      (MvPolynomial.rename Sum.inl A).vars := by
  intro h
  obtain ⟨j, _hj, hji⟩ := MvPolynomial.mem_vars_rename Sum.inl A h
  exact Sum.inl_ne_inr hji

private theorem input_notMem_targetVars
    {R tau sigma : Type*} [CommRing R]
    (i : sigma) (A : MvPolynomial tau R) :
    (Sum.inr (Sum.inr i) : PaperThreeBlock tau sigma) ∉
      (MvPolynomial.rename Sum.inl A).vars := by
  intro h
  obtain ⟨j, _hj, hji⟩ := MvPolynomial.mem_vars_rename Sum.inl A h
  exact Sum.inl_ne_inr hji

/-- One source/input contraction passes through a target-only multiplicative
spectator and through the embedding of the fixed two-block calculation. -/
private theorem contractVariables_targetMul_rename
    {R tau sigma : Type*} [CommRing R]
    (i : sigma) (A : MvPolynomial tau R)
    (P : MvPolynomial (sigma ⊕ sigma) R) :
    contractVariables (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr i))
        (MvPolynomial.rename Sum.inl A * MvPolynomial.rename Sum.inr P) =
      MvPolynomial.rename Sum.inl A *
        MvPolynomial.rename Sum.inr
          (contractVariables (Sum.inl i) (Sum.inr i) P) := by
  unfold contractVariables
  rw [MvPolynomial.specializeZero_mul,
    MvPolynomial.specializeZero_eq_self_of_notMem_vars
      (Sum.inr (Sum.inl i)) (MvPolynomial.rename Sum.inl A)
      (source_notMem_targetVars i A),
    MvPolynomial.specializeZero_rename Sum.inr Sum.inr_injective,
    MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (source_notMem_targetVars i A),
    MvPolynomial.pderiv_rename Sum.inr_injective]
  simp only [zero_mul, zero_add]
  rw [MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (input_notMem_targetVars i A),
    MvPolynomial.pderiv_rename Sum.inr_injective]
  simp only [zero_mul, zero_add, map_sub, mul_sub]

/-- The fixed two-block contraction calculation lifts through arbitrary target
spectators in the three-block ambient variable type. -/
theorem contractMappedVariablePairs_targetMul_rename
    {R tau sigma : Type*} [CommRing R]
    (l : List sigma) (A : MvPolynomial tau R)
    (P : MvPolynomial (sigma ⊕ sigma) R) :
    contractMappedVariablePairs paperSourceEmbedding paperInputEmbedding l
        (MvPolynomial.rename paperTargetEmbedding A *
          MvPolynomial.rename Sum.inr P) =
      MvPolynomial.rename paperTargetEmbedding A *
        MvPolynomial.rename Sum.inr (contractVariablePairs l P) := by
  induction l generalizing P with
  | nil => rfl
  | cons i l ih =>
      change contractMappedVariablePairs paperSourceEmbedding
          paperInputEmbedding l
          (contractVariables (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr i))
            (MvPolynomial.rename Sum.inl A * MvPolynomial.rename Sum.inr P)) =
        MvPolynomial.rename Sum.inl A *
          MvPolynomial.rename Sum.inr
            (contractVariablePairs l
              (contractVariables (Sum.inl i) (Sum.inr i) P))
      rw [contractVariables_targetMul_rename, ih]

/-- The sign contributed by `(-w)^m` cancels the sign in the fixed-pair
Lieb--Sokal contraction formula. -/
theorem contractVariablePairs_signedBasisMonomial
    {sigma : Type*} [Fintype sigma]
    (m : OneBox sigma) (G : MvPolynomial sigma ℂ) :
    contractVariablePairs (differentialVariableOrder sigma)
        (pairedProduct (signedBasisMonomial m) G) =
      MvPolynomial.rename Sum.inr
        (applyMonomialDifferential m.1 G) := by
  classical
  change contractVariablePairs (differentialVariableOrder sigma)
      (pairedProduct
        (MvPolynomial.monomial m.1
          ((-1 : ℂ) ^ (m.1.sum fun _ n => n))) G) = _
  rw [contractVariablePairs_pairedProduct_monomial
    (differentialVariableOrder sigma)
    (nodup_differentialVariableOrder sigma) m.1
    (by intro i hi; simp) m.2
    ((-1 : ℂ) ^ (m.1.sum fun _ n => n)) G,
    listExponentSum_differentialVariableOrder,
    applyMonomialDifferentialAlong_differentialVariableOrder]
  have hsign :
      (-1 : ℂ) ^ (m.1.sum fun _ n => n) *
          (-1 : ℂ) ^ (m.1.sum fun _ n => n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hsign]
  simp

/-- One summand of the paper's reciprocal-symbol product contracts to the
corresponding target coefficient times the source derivative of the input. -/
theorem contractMappedVariablePairs_paperSummand
    {tau sigma : Type*} [Fintype sigma]
    (m : OneBox sigma) (A : MvPolynomial tau ℂ)
    (G : MvPolynomial sigma ℂ) :
    contractMappedVariablePairs paperSourceEmbedding paperInputEmbedding
        (differentialVariableOrder sigma)
        (MvPolynomial.rename paperTargetEmbedding A *
          MvPolynomial.rename Sum.inr
            (pairedProduct (signedBasisMonomial m) G)) =
      MvPolynomial.rename paperTargetInputEmbedding
        (MvPolynomial.rename Sum.inl A *
          MvPolynomial.rename Sum.inr
            (applyMonomialDifferential m.1 G)) := by
  rw [contractMappedVariablePairs_targetMul_rename,
    contractVariablePairs_signedBasisMonomial]
  simp [paperTargetInputEmbedding, paperTargetEmbedding,
    paperInputEmbedding, Function.comp_def]

/-- The three-block polynomial
`sum_m T(z^m) (-w)^m f(v)` from Lemma 2.2. -/
def paperThreeBlock
    {tau sigma : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1)) :
    MvPolynomial (PaperThreeBlock tau sigma) ℂ :=
  ∑ m : OneBox sigma,
    MvPolynomial.rename paperTargetEmbedding
        (T (MvPolynomial.basisDegreeOfLE
          (R := ℂ) (fun _ : sigma => 1) m)) *
      MvPolynomial.rename Sum.inr
        (pairedProduct (signedBasisMonomial m) f.1)

/-- The target/input polynomial
`sum_m T(z^m) (partial^m f)(v)` obtained after all contractions. -/
def paperDifferentialSum
    {tau sigma : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1)) :
    MvPolynomial (tau ⊕ sigma) ℂ :=
  ∑ m : OneBox sigma,
    MvPolynomial.rename Sum.inl
        (T (MvPolynomial.basisDegreeOfLE
          (R := ℂ) (fun _ : sigma => 1) m)) *
      MvPolynomial.rename Sum.inr
        (applyMonomialDifferential m.1 f.1)

/-- Repeated mapped contraction performs exactly the suppressed
Lieb--Sokal calculation in Borcea--Branden, Lemma 2.2. -/
theorem contractMappedVariablePairs_paperThreeBlock
    {tau sigma : Type*} [Fintype sigma]
    (T : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial tau ℂ)
    (f : MvPolynomial.degreeOfLE sigma ℂ (fun _ => 1)) :
    contractMappedVariablePairs paperSourceEmbedding paperInputEmbedding
        (differentialVariableOrder sigma) (paperThreeBlock T f) =
      MvPolynomial.rename paperTargetInputEmbedding
        (paperDifferentialSum T f) := by
  classical
  rw [paperThreeBlock, contractMappedVariablePairs_sum,
    paperDifferentialSum, map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  exact contractMappedVariablePairs_paperSummand m
    (T (MvPolynomial.basisDegreeOfLE
      (R := ℂ) (fun _ : sigma => 1) m)) f.1

end BorceaBranden

end

end RealRooted
